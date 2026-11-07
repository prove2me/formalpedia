-- Prove2me | Theorems.Thm_NCPComm_claim_4_10
-- name    : NCPComm.claim_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:02:59.545735+00:00
-- url     : https://prove2.me/theorems/0e204745-4939-4231-9a60-aef879967977
-- title:
--   Claim 4.10 — the setups for $b=0$ and $b=1$ agree except on light doubletons
-- statement:
--   Let $s=\Omega(\sqrt N)$ and $K,s=o(N)$. Then
--
--   1. $\delta_{\mathrm{TV}}\big((\mathbf H^1_1,\dots,\mathbf H^1_s),(\mathbf H^0_1,\dots,\mathbf H^0_s)\big)=0$;
--   2. $\delta_{\mathrm{TV}}\big((\mathbf L^1_3,\dots,\mathbf L^1_s),(\mathbf L^0_3,\dots,\mathbf L^0_s)\big)=O(s^3/N^2)$;
--   3. $\delta_{\mathrm{TV}}(\mathbf L^1_1,\mathbf L^0_1)=O(s^{3/2}/N)$.
--
--   The only remaining difference between the two cases is therefore in $\mathbf L^b_2$, the light doubletons.
--
--   **Formalization Note** The comparisons are of full vectors, as on the page, and not of their counts.
--
--   Differences from the source:
--   - encoding: labels in [N] = {1,…,N} → Fin N, 0-based; reason: Lean convention; same objects
--   - encoding: multiplicity indicators (v_i)_i → the count function on labels, with v_i(x) = 1 iff the count at x is i; reason: the two determine each other, and s′ is the total of the counts
--   - encoding: asymptotic statement in N with o(·), O(·), Ω(·) → sequences N(n), K(n), s(n) with limits and "for all large n"; reason: decision 11 of the plan; a family of parameters is what the asymptotic notation quantifies over
--   - encoding: the regime of §4: N ∈ 6ℕ → 3 ∣ N and 0 < K (with 3K < N eventually, from K = o(N)); reason: p.19 calls divisibility by 6 "only for convenience", and N ∈ 3ℕ is what Proposition 4.7 uses; N ∈ 6ℕ is a special case
--   - encoding: D uniform on F_b(N, K) → π uniform on permutations, D = π(D_b); reason: the orbit map pushes the uniform law to the uniform law on the orbit; the page reads the randomness as "the heavy and light sets"
--   - generalization: the first item under s = Ω(√N) and K, s = o(N) → the first item at every valid (N, K, s); reason: the proof uses only that heavy parts have the same law; the regime is a special case
--   - reading: (…_1, …, …_s) with s the Poisson mean → the whole families of multiplicities; reason: s′ can exceed s; Definition 4.5 indexes by the sample, and Proposition 4.7 uses s′ (decision 13)
--   - reading: O(·) with a constant unnamed on the page → ∃ C depending only on the constant c of s = Ω(√N), quantified before the sequences, with the bound for all large n; reason: the stronger reading; the proof's constants are absolute (union bound, Claims 3.11 and 3.18) except for the step 1/√s = O(s^{3/2}/N), which uses s ≥ c√N
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Claim 4.10, p.24

import Mathlib
import Definitions.Def_NCPComm_idealSetup

open scoped NNReal ENNReal Topology
open Filter

namespace NCPComm

/-- **Claim 4.10, p.24** (Herman, The Communication Complexity of Verifying Distribution Properties,
STOC 2027 submission, manuscript sha256 714c0353…). Under `s = Ω(√N)` and `K, s = o(N)`:
1. the heavy families `(H¹_i)_i` and `(H⁰_i)_i` have the same law;
2. `δ_TV((L¹_i)_{i≥3}, (L⁰_i)_{i≥3}) = O(s³/N²)`;
3. `δ_TV(L¹₁, L⁰₁) = O(s^{3/2}/N)`.

**Formalization Note** The first item holds at every valid parameter, which is more general than
the page's regime. Tuples `(…_1, …, …_s)` are the whole multiplicity families, encoded as count
functions. Parameters are sequences. The `O` constant `C` depends only on the constant `c` of
`s = Ω(√N)`: it is quantified after `c` and before the sequences, and only the threshold in `n`
depends on the sequence. `3 ∣ N` and `0 < K` are the standing assumptions of p.19; `3K < N` follows
for large `n` from `K = o(N)`. -/
theorem claim_4_10 :
    (∀ (N K : ℕ) (s : ℝ≥0), ValidParams N K →
      OAI.ThreeState.tvMass ((idealSetup true N K s).map heavyPart)
        ((idealSetup false N K s).map heavyPart) = 0) ∧
    (∀ c : ℝ, 0 < c → ∃ C : ℝ, ∀ (N K : ℕ → ℕ) (s : ℕ → ℝ≥0),
      (∀ᶠ n in atTop, 3 ∣ N n ∧ 0 < K n) →
      (∀ᶠ n in atTop, c * Real.sqrt (N n) ≤ (s n : ℝ)) →
      Tendsto (fun n => (K n : ℝ) / N n) atTop (𝓝 0) →
      Tendsto (fun n => (s n : ℝ) / N n) atTop (𝓝 0) →
      (∀ᶠ n in atTop,
        OAI.ThreeState.tvMass ((idealSetup true (N n) (K n) (s n)).map lightHigh)
            ((idealSetup false (N n) (K n) (s n)).map lightHigh)
          ≤ C * ((s n : ℝ) ^ 3 / (N n : ℝ) ^ 2)) ∧
      (∀ᶠ n in atTop,
        OAI.ThreeState.tvMass ((idealSetup true (N n) (K n) (s n)).map fun o => lightIndicator o 1)
            ((idealSetup false (N n) (K n) (s n)).map fun o => lightIndicator o 1)
          ≤ C * ((s n : ℝ) ^ (3 / 2 : ℝ) / (N n : ℝ)))) := by sorry

end NCPComm
