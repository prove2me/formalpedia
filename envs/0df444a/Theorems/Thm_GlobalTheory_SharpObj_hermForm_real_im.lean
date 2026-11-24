-- Prove2me | Theorems.Thm_GlobalTheory_SharpObj_hermForm_real_im
-- name    : GlobalTheory.SharpObj.hermForm_real_im
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:11:07.418798+00:00
-- url     : https://prove2.me/theorems/6374218b-9134-417f-b9ce-0e0027afc499
-- title:
--   Sharp Obj: herm Form real im
-- statement:
--   The Sharp Obj construction uses the herm Form real im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImInvIsHermitian.lean#L39-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImInvIsHermitian.lean#L39-L47

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

theorem GlobalTheory.SharpObj.hermForm_real_im (M : Matrix (Fin h) (Fin h) ℝ) (z w : Fin h → ℂ) :
    (hermForm (M.map fun x : ℝ => (x : ℂ)) z w).im =
      (fun i => (z i).im) ⬝ᵥ M.mulVec (fun i => (w i).re) - (fun i => (z i).re) ⬝ᵥ M.mulVec (fun i => (w i).im) := by sorry
