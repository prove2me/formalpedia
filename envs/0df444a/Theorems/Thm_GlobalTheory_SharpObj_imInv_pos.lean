-- Prove2me | Theorems.Thm_GlobalTheory_SharpObj_imInv_pos
-- name    : GlobalTheory.SharpObj.imInv_pos
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:11:05.43894+00:00
-- url     : https://prove2.me/theorems/97e441da-2d7e-4d21-8753-f6bb8e7df02d
-- title:
--   Sharp Obj: im Inv pos
-- statement:
--   The Sharp Obj construction uses the im Inv pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImInvIsHermitian.lean#L55-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImInvIsHermitian.lean#L55-L74

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
variable {τ : Matrix (Fin h) (Fin h) ℂ}

theorem GlobalTheory.SharpObj.imInv_pos (hp : (τ.map Complex.im).PosDef) (z : Fin h → ℂ) (hz : z ≠ 0) :
    0 < (hermForm (imInv τ) z z).re := by sorry
