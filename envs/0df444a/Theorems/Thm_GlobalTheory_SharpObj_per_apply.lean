-- Prove2me | Theorems.Thm_GlobalTheory_SharpObj_per_apply
-- name    : GlobalTheory.SharpObj.per_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:11:21.794299+00:00
-- url     : https://prove2.me/theorems/ddd45ef7-e9e0-45bb-94e5-62bd73eeaebe
-- title:
--   Sharp Obj: per apply
-- statement:
--   The Sharp Obj construction uses the per apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImInvIsHermitian.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImInvIsHermitian.lean#L23-L24

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

theorem GlobalTheory.SharpObj.per_apply (τ : Matrix (Fin h) (Fin h) ℂ) (x : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    per τ x i = τ.mulVec (fun i' => (x (.inl i') : ℂ)) i + (x (.inr i) : ℂ) := by sorry
