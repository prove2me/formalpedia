-- Prove2me | Theorems.Thm_GlobalTheory_SharpObj_per_eq
-- name    : GlobalTheory.SharpObj.per_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:25:47.078132+00:00
-- url     : https://prove2.me/theorems/1a5a8025-9416-4ff4-b0a5-97ece794253c
-- title:
--   Sharp Obj: per eq
-- statement:
--   The Sharp Obj construction uses the per eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImInvIsHermitian.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImInvIsHermitian.lean#L76-L81

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

theorem GlobalTheory.SharpObj.per_eq (x : Fin h ⊕ Fin h → ℤ) :
    per τ x = τ.mulVec (ReciprocityTheory.PTheta.ofRealVec fun i => (x (.inl i) : ℝ)) +
      ReciprocityTheory.PTheta.ofRealVec fun i => (x (.inr i) : ℝ) := by sorry
