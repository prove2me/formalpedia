-- Prove2me | Theorems.Thm_GlobalTheory_TorsionMatrix_norm_det_eq
-- name    : GlobalTheory.TorsionMatrix.norm_det_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T17:08:14.232543+00:00
-- url     : https://prove2.me/theorems/85fa5871-79a7-4a49-958e-d7276e6e434c
-- title:
--   Torsion Matrix: norm det eq
-- statement:
--   The Torsion Matrix construction uses the norm det eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MatrixPolynomialDetNormFixedPoints.lean#L255-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MatrixPolynomialDetNormFixedPoints.lean#L255-L316

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NormCardQuotientSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MatrixPolynomialDetNormFixedPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.TorsionMatrix
open Matrix

theorem GlobalTheory.TorsionMatrix.norm_det_eq (l : ℕ) [hl : Fact l.Prime] {κ Q : Type} [Fintype κ] [DecidableEq κ]
    [AddCommGroup Q] (τ : κ → ℕ → Q) (h1 : ∀ i n, (l ^ (n + 1)) • τ i n = 0)
    (hb : ∀ n (x : Q), (l ^ (n + 1)) • x = 0 →
      ∃! t : κ → ZMod (l ^ (n + 1)), ∑ j, (t j).val • τ j n = x)
    (f : Q →+ Q) (M : Matrix κ κ ℤ_[l])
    (hM : ∀ j n, f (τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (M k j)).val • τ k n)
    [Finite f.ker] : ‖M.det‖ = ‖((Nat.card f.ker : ℕ) : ℚ_[l])‖ := by sorry
