-- Prove2me | Theorems.Thm_GlobalTheory_SharpObj_exists_form
-- name    : GlobalTheory.SharpObj.exists_form
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:10:40.897764+00:00
-- url     : https://prove2.me/theorems/bb881b2f-0dce-40c9-b689-2579ab888fb5
-- title:
--   Sharp Obj: exists form
-- statement:
--   The Sharp Obj construction uses the exists form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImInvIsHermitian.lean#L224-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImInvIsHermitian.lean#L224-L273

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

theorem GlobalTheory.SharpObj.exists_form (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    ∃ Ef : LinearMap.BilinForm ℤ (LinearMap.range (per τ)),
      (∀ a b : LinearMap.range (per τ), (Ef a b : ℝ) = (hermForm (imInv τ) a b).im) ∧ Function.Bijective Ef := by sorry
