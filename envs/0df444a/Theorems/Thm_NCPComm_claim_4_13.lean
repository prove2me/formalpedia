-- Prove2me | Theorems.Thm_NCPComm_claim_4_13
-- name    : NCPComm.claim_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:10.380196+00:00
-- url     : https://prove2.me/theorems/d1ef10bf-15b3-43c8-8963-569c19e387c4
-- title:
--   Claim 4.13 — final doubleton counts and their distances from the ideal NO counts
-- statement:
--   Assume the parameters of Proposition 4.7 at source $(N,K,s)$, with $s\ge C_1\sqrt N$ for a sufficiently large absolute constant $C_1$. Let $h_i,\ell_i$ be the unconditioned counts of Alice's canonical sample, and let the ideal vectors use parameters $(2N,2K)$, with $g:=\lfloor\mathbb E[|\mathbf L^1_2|]-\mathbb E[|\mathbf L^0_2|]+\frac12\rfloor$.
--
--   1. On executions that do not abort, the final heavy and light doubleton counts are $h_2-\langle a,b\rangle$ and $\ell_2+\langle a,b\rangle$; in particular $h_2,\ell_2$ when $\langle a,b\rangle=0$ and $h_2-g,\ell_2+g$ when $\langle a,b\rangle=g$.
--   2. $\delta_{\mathrm{TV}}\big((h_2,\ell_2),(|\mathbf H^0_2|,|\mathbf L^0_2|)\big)=0$.
--   3. $\delta_{\mathrm{TV}}(h_2-g,|\mathbf H^1_2|)=O(g\sqrt K/s)=o(1)$ and $\delta_{\mathrm{TV}}(\ell_2+g,|\mathbf L^1_2|)\le0.269$.
--   4. Jointly over all multiplicities,
--   $$
--   \delta_{\mathrm{TV}}\big((h_i-g\mathbf 1_{\{i=2\}})_{i\ge1},(|\mathbf H^1_i|)_{i\ge1}\big)=o(1),\qquad
--   \delta_{\mathrm{TV}}\big((\ell_i+g\mathbf 1_{\{i=2\}})_{i\ge1},(|\mathbf L^1_i|)_{i\ge1}\big)\le0.269+o(1).
--   $$
--
--   **Formalization Note** Differences take values in $\mathbb Z$. The first item is a deterministic identity, stated for any canonical outcome and written with addition.
--
--   Differences from the source:
--   - encoding: D uniform on F_b(N, K) → π uniform on permutations, D = π(D_b); reason: the orbit map pushes the uniform law to the uniform law on the orbit; the page reads the randomness as "the heavy and light sets"
--   - encoding: asymptotic statement in N with o(·), O(·), Ω(·) → sequences N(n), K(n), s(n) with limits and "for all large n"; reason: decision 11 of the plan; a family of parameters is what the asymptotic notation quantifies over
--   - encoding: multiplicity indicators (v_i)_i → the count function on labels, with v_i(x) = 1 iff the count at x is i; reason: the two determine each other, and s′ is the total of the counts
--   - generalization: final counts for ⟨a, b⟩ ∈ {0, g} → final counts for every value of ⟨a, b⟩, and for any canonical sample outcome; reason: the identity is deterministic, and r = 0 and r = g are the instances the page names
--   - generalization: item 2 under the parameters of Proposition 4.7 → item 2 at every valid (2N, 2K, s); reason: relabelling by π changes no count, so the regime is not needed; the regime is a special case
--   - reading: O(g√K/s) with a constant unnamed on the page → ∃ C absolute, quantified with C₁ before the sequences, with the bound for all large n; reason: the stronger reading; the proof's mean-shift bound uses only absolute constants (Claims 3.11, 3.17, 3.18) and σ_h ∼ s/(4√K)
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Claim 4.13, p.27

import Mathlib
import Definitions.Def_NCPComm_setupProcedure

open scoped NNReal ENNReal Topology
open Filter

namespace NCPComm

/-- **Claim 4.13, p.27** (Herman, The Communication Complexity of Verifying Distribution Properties,
STOC 2027 submission, manuscript sha256 714c0353…). Let `h_i, ℓ_i` be the counts of Alice's canonical
sample from `D₀([2K])` over `[2N]`, and write `r = ⟨a, b⟩`.
1. On every execution that does not abort, the final heavy doubleton count is `h₂ - r` and the final
   light doubleton count is `ℓ₂ + r`, for every `r`, in particular `r = 0` and `r = g`.
2. `δ_TV((h₂, ℓ₂), (|H⁰₂|, |L⁰₂|)) = 0`.
3. For `s ≥ C₁√N` with an absolute `C₁`, in the parameters of Proposition 4.7, with
   `g := ⌊E[|L¹₂|] - E[|L⁰₂|] + 1/2⌋` at `(2N, 2K)`: `δ_TV(h₂ - g, |H¹₂|) = O(g√K/s) = o(1)`,
   `δ_TV(ℓ₂ + g, |L¹₂|) ≤ 0.269`, and jointly over all multiplicities
   `δ_TV((h_i - g1_{i=2})_{i≥1}, (|H¹_i|)_{i≥1}) = o(1)` and
   `δ_TV((ℓ_i + g1_{i=2})_{i≥1}, (|L¹_i|)_{i≥1}) ≤ 0.269 + o(1)`.

**Formalization Note** Differences such as `h₂ - g` take values in `ℤ`. The first item is a
deterministic identity for any canonical sample outcome `o`, written with addition to avoid `ℕ`
subtraction. The ideal vectors use parameters `(2N, 2K)`. The constant `C` of `O(g√K/s)` is
absolute, quantified with `C₁` before the sequences; only the thresholds in `n` and the `o(1)`
sequence depend on the sequence. -/
theorem claim_4_13 :
    (∀ (N K : ℕ) (a b : Fin N → Bool) (π : Equiv.Perm (Fin (2 * N))) (o : SetupOutcome (2 * N))
        (w : Fin (2 * N) → ℕ),
      0 < K → 3 * K < N → aliceCounts N K a o = some w →
      let o' : SetupOutcome (2 * N) :=
        ⟨bobLight N K b π, bobHeavy N K b π, fun y => w (π.symm y)⟩
      heavyCount o' 2 + innerCount a b = heavyCount o 2 ∧
      lightCount o' 2 = lightCount o 2 + innerCount a b) ∧
    (∀ (N K : ℕ) (s : ℝ≥0), ValidParams (2 * N) (2 * K) →
      OAI.ThreeState.tvMass
          ((canonicalSetup (2 * N) (2 * K) s).map fun o => (heavyCount o 2, lightCount o 2))
          ((idealSetup false (2 * N) (2 * K) s).map fun o => (heavyCount o 2, lightCount o 2))
        = 0) ∧
    (∃ C₁ C : ℝ, 0 < C₁ ∧ ∀ (K : ℕ → ℕ) (s : ℕ → ℝ≥0), InRegime C₁ K s →
      let N : ℕ → ℕ := fun n => 3 * n
      let g : ℕ → ℕ := fun n => gapFromMeans (2 * N n) (2 * K n) (s n)
      (∀ᶠ n in atTop,
        OAI.ThreeState.tvMass
            ((canonicalSetup (2 * N n) (2 * K n) (s n)).map fun o =>
              (heavyCount o 2 : ℤ) - (g n : ℤ))
            ((idealSetup true (2 * N n) (2 * K n) (s n)).map fun o => (heavyCount o 2 : ℤ))
          ≤ C * ((g n : ℝ) * Real.sqrt (K n) / (s n : ℝ))) ∧
      Tendsto (fun n => (g n : ℝ) * Real.sqrt (K n) / (s n : ℝ)) atTop (𝓝 0) ∧
      (∀ᶠ n in atTop,
        OAI.ThreeState.tvMass
            ((canonicalSetup (2 * N n) (2 * K n) (s n)).map fun o =>
              (lightCount o 2 : ℤ) + (g n : ℤ))
            ((idealSetup true (2 * N n) (2 * K n) (s n)).map fun o => (lightCount o 2 : ℤ))
          ≤ 0.269) ∧
      Tendsto (fun n => OAI.ThreeState.tvMass
          ((canonicalSetup (2 * N n) (2 * K n) (s n)).map fun o =>
            doubletonShift (-(g n : ℤ)) (heavyHist o))
          ((idealSetup true (2 * N n) (2 * K n) (s n)).map heavyHist)) atTop (𝓝 0) ∧
      (∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
        OAI.ThreeState.tvMass
            ((canonicalSetup (2 * N n) (2 * K n) (s n)).map fun o =>
              doubletonShift (g n : ℤ) (lightHist o))
            ((idealSetup true (2 * N n) (2 * K n) (s n)).map lightHist)
          ≤ 0.269 + ε n)) := by sorry

end NCPComm
