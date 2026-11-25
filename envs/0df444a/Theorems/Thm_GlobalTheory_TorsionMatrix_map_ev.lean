-- Prove2me | Theorems.Thm_GlobalTheory_TorsionMatrix_map_ev
-- name    : GlobalTheory.TorsionMatrix.map_ev
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:15:59.367922+00:00
-- url     : https://prove2.me/theorems/00204fbe-041d-5886-a2e4-37b179d76aec
-- title:
--   Torsion Matrix: map ev
-- statement:
--   The Torsion Matrix construction uses the map ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MatrixPolynomialDetNormFixedPoints.lean#L214-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MatrixPolynomialDetNormFixedPoints.lean#L214-L223

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
variable {Q κ : Type} [AddCommGroup Q] [Fintype κ] {N : ℕ} [NeZero N]

theorem GlobalTheory.TorsionMatrix.map_ev (g : Q →+ Q) {pt pt' : κ → Q} (h : ∀ i, N • pt i = 0) (h' : ∀ i, N • pt' i = 0)
    (M : Matrix κ κ (ZMod N)) (hM : ∀ j, g (pt j) = ∑ i, (M i j).val • pt' i) (t : κ → ZMod N) :
    g (ev pt h t) = ev pt' h' (M *ᵥ t) := by sorry
