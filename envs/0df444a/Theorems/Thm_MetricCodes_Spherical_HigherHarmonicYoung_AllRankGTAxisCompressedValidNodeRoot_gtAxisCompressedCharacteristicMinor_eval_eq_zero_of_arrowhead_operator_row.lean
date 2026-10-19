-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTAxisCompressedValidNodeRoot_gtAxisCompressedCharacteristicMinor_eval_eq_zero_of_arrowhead_operator_row
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedValidNodeRoot.gtAxisCompressedCharacteristicMinor_eval_eq_zero_of_arrowhead_operator_row
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:15.843669+00:00
-- url     : https://prove2.me/theorems/0babc034-beab-4a7c-a5d5-bac01acc75ed
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedValidNodeRoot.gtAxisCompressedCharacteristicMinor_eval_eq_zero_of_arrowhead_operator_row
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 700000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedValidNodeRoot
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedValidNodeRoot.gtAxisCompressedCharacteristicMinor_eval_eq_zero_of_arrowhead_operator_row
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (node : ℝ)
    (coupling : Module.End ℝ (HarmonicYoungSpace (n := n) mu))
    (hcoupling : Function.Injective coupling)
    (horth : B.adjoint
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram q) = 0)
    (hchar :
      Polynomial.aeval (gtRelativeCasimir (n := n + 1) lam)
        (gtChannelCharacteristicPolynomial (n + 1) lam)
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram q) = 0)
    (hrow : ∀ x : SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam,
      B.adjoint (gtRelativeCasimir (n := n + 1) lam x) =
        node • B.adjoint x +
          coupling ((canonicalGelfandTsetlinAxisTensor
            lam mu h hgram).adjoint x)) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval node = 0 := by sorry
