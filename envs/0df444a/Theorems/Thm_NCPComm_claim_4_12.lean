-- Prove2me | Theorems.Thm_NCPComm_claim_4_12
-- name    : NCPComm.claim_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:03:15.023271+00:00
-- url     : https://prove2.me/theorems/4d8e879a-ed75-475c-8874-3b872bfd5f4a
-- title:
--   Claim 4.12 — the shifted light doubleton counts are within 0.269
-- statement:
--   There is an absolute constant $C_0$ such that, if $s\ge C_0\sqrt N$ and $K,s=o(N)$, then with
--   $$
--   g:=\big\lfloor\mathbb E[|\mathbf L^1_2|]-\mathbb E[|\mathbf L^0_2|]+\tfrac12\big\rfloor,
--   $$
--   for all sufficiently large $N$,
--   $$
--   \delta_{\mathrm{TV}}(|\mathbf L^0_2|+g,|\mathbf L^1_2|)\le0.269.
--   $$
--
--   This is the quantitative heart of the reduction: after a shift by $g$, the two doubleton counts cannot be told apart with advantage beyond the $0.269$ allowed.
--
--   **Formalization Note** $g$ is `Nat.floor`, which equals the integer floor since the mean difference is positive in this regime.
--
--   Differences from the source:
--   - encoding: D uniform on F_b(N, K) → π uniform on permutations, D = π(D_b); reason: the orbit map pushes the uniform law to the uniform law on the orbit; the page reads the randomness as "the heavy and light sets"
--   - encoding: the regime of §4: N ∈ 6ℕ → 3 ∣ N and 0 < K (with 3K < N eventually, from K = o(N)); reason: p.19 calls divisibility by 6 "only for convenience", and N ∈ 3ℕ is what Proposition 4.7 uses; N ∈ 6ℕ is a special case
--   - encoding: asymptotic statement in N with o(·), O(·), Ω(·) → sequences N(n), K(n), s(n) with limits and "for all large n"; reason: decision 11 of the plan; a family of parameters is what the asymptotic notation quantifies over
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Claim 4.12, p.26; proof, pp.26–27

import Mathlib
import Definitions.Def_NCPComm_idealSetup

open scoped NNReal ENNReal Topology
open Filter

namespace NCPComm

/-- **Claim 4.12, pp.26–27** (Herman, The Communication Complexity of Verifying Distribution
Properties, STOC 2027 submission, manuscript sha256 714c0353…). There is an absolute `C₀` such that,
if `s ≥ C₀√N` and `K, s = o(N)`, then with `g := ⌊E[|L¹₂|] - E[|L⁰₂|] + 1/2⌋`, for all sufficiently
large `N`, `δ_TV(|L⁰₂| + g, |L¹₂|) ≤ 0.269`.

**Formalization Note** `C₀` is placed before the sequences. `3 ∣ N` and `0 < K` are the standing
assumptions of p.19. -/
theorem claim_4_12 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (N K : ℕ → ℕ) (s : ℕ → ℝ≥0),
      (∀ᶠ n in atTop, 3 ∣ N n ∧ 0 < K n) →
      (∀ᶠ n in atTop, C₀ * Real.sqrt (N n) ≤ (s n : ℝ)) →
      Tendsto (fun n => (K n : ℝ) / N n) atTop (𝓝 0) →
      Tendsto (fun n => (s n : ℝ) / N n) atTop (𝓝 0) →
      ∀ᶠ n in atTop,
        OAI.ThreeState.tvMass
            ((idealSetup false (N n) (K n) (s n)).map fun o =>
              lightCount o 2 + gapFromMeans (N n) (K n) (s n))
            ((idealSetup true (N n) (K n) (s n)).map fun o => lightCount o 2)
          ≤ 0.269 := by sorry

end NCPComm
