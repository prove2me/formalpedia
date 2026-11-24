-- Prove2me | Theorems.Thm_GlobalTheory_SharpObj_hermForm_real_re
-- name    : GlobalTheory.SharpObj.hermForm_real_re
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:10:42.946796+00:00
-- url     : https://prove2.me/theorems/b539dea3-f50c-463f-9ec3-0e7c253b6d70
-- title:
--   Sharp Obj: herm Form real re
-- statement:
--   The Sharp Obj construction uses the herm Form real re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImInvIsHermitian.lean#L29-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImInvIsHermitian.lean#L29-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ImInvIsHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SharpObj
variable {h : ℕ}

theorem GlobalTheory.SharpObj.hermForm_real_re (M : Matrix (Fin h) (Fin h) ℝ) (z w : Fin h → ℂ) :
    (hermForm (M.map fun x : ℝ => (x : ℂ)) z w).re =
      (fun i => (z i).re) ⬝ᵥ M.mulVec (fun i => (w i).re) + (fun i => (z i).im) ⬝ᵥ M.mulVec (fun i => (w i).im) := by sorry
