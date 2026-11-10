-- Prove2me | Theorems.Thm_HGASUndecidable_Main_lemma_7_3
-- name    : HGASUndecidable.Main.lemma_7_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:16:13.13199+00:00
-- url     : https://prove2.me/theorems/f905b3a8-6c98-4524-906a-d45295ea5280
-- title:
--   Lemma 7.3 — De has absolutely convergent Fourier series; constant coefficient Σ_{solutions} (λη)^{|n|²}, positive iff e ∈ K
-- statement:
--   Use λ=1/256 and η=1/2, and the function D_e defined by (7.5)–(7.7). Fix any data satisfying Lemma 7.2. Lemma 7.3 (Positive constant Fourier coefficient). The Fourier series of De converges absolutely, and its constant Fourier coefficient is (D̂e)_{(0,...,0)} = (1/(2π)^{q+r}) ∫_{T^{q+r}} De(φ) dφ = Σ_{n∈Z^q, An^{◦2}+Bn=c(e)} (λη)^{|n|²}. (7.8) In particular (D̂e)_{(0,...,0)} is a positive real number if e ∈ K, and it is zero if e ∉ K.
--
--   Differences from the source:
--   - encoding: the halting set of a universal Turing machine on paired input → definedness of (Nat.Partrec.Code.ofNatCode e.unpair.1).eval e.unpair.2; reason: this is the universal partial-recursive halting problem, with the same many-one completeness convention
--   - encoding: functions on (ℝ/2πℤ)ᵈ and normalized torus integration → 2π-periodic functions on Fin d → ℝ, integrated on [0,2π]ᵈ with the factor (2π)⁻ᵈ; reason: the boundaries have measure zero, and this is the same normalized Haar integral and Fourier convention
--   - generalization: the fixed data q,r,A,B,c₀,c₁ chosen after Lemma 7.2 → every DiophantineData satisfying positivity, nonzero columns of B, and the halting-solvability equivalence; reason: the subsequent construction and assertions use exactly these properties and specialize to the fixed source choice
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), Lemma 7.3, printed p. 38 (PDF 40)

import Definitions.Def_HGASUndecidable_Main_Fourier

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

theorem lemma_7_3 (a : DiophantineData) (ha : DiophantineValid a) (e : ℕ) :
    AbsolutelyConvergentFourier (torusFunction a e) ∧
    fourierCoeff (torusFunction a e) 0 =
      ∑' v : {v : Fin a.q → ℤ // DiophantineSolution a e v},
        ((lambda*eta : ℝ) : ℂ) ^ (∑ j, (v.val j).natAbs^2) ∧
    (haltingSet e → (fourierCoeff (torusFunction a e) 0).im = 0 ∧
      0 < (fourierCoeff (torusFunction a e) 0).re) ∧
    (¬haltingSet e → fourierCoeff (torusFunction a e) 0 = 0) := by sorry

end HGASUndecidable.Main
