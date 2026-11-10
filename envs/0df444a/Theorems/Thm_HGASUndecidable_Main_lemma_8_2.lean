-- Prove2me | Theorems.Thm_HGASUndecidable_Main_lemma_8_2
-- name    : HGASUndecidable.Main.lemma_8_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:16:16.908083+00:00
-- url     : https://prove2.me/theorems/dffc6ee2-2ad6-42ae-ab0a-6df2e35cad69
-- title:
--   Lemma 8.2 — |Σ k_a ϵ_a √p_a| ≥ (√P |k|_1)^{1−2^d} > 0 for distinct primes
-- statement:
--   Lemma 8.2. Let p1, . . . , pd be distinct primes, P = max_a p_a, ϵ ∈ {−1, 1}^d and k ∈ Z^d \ {0}. Then |Σ_{a=1}^{d} k_a ϵ_a √p_a| ≥ (√P |k|_1)^{1−2^d} > 0, |k|_1 = Σ_a |k_a|. (8.2)
--
--   Differences from the source:
--   - encoding: the maximum of the distinct primes p₁,…,p_d → Finset.univ.sup p on zero-based indices; the exponent 1−2^d is an integer; reason: k ≠ 0 rules out d = 0, so the supremum is the nonempty maximum and the exponent does not use truncated natural subtraction
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), Lemma 8.2, printed p. 41 (PDF 43)

import Definitions.Def_HGASUndecidable_Main_Fourier

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

theorem lemma_8_2 {d : ℕ} (p : Fin d → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hd : Function.Injective p) (ε : Fin d → ℤ) (hε : ∀ i, ε i = -1 ∨ ε i = 1)
    (k : Fin d → ℤ) (hk : k ≠ 0) :
    let P := Finset.univ.sup p
    let b := (Real.sqrt P * ∑ i, |(k i : ℝ)|) ^ (1-(2:ℤ)^d)
    b ≤ |∑ i, (k i : ℝ)*(ε i : ℝ)*Real.sqrt (p i)| ∧ 0 < b := by sorry

end HGASUndecidable.Main
