-- Prove2me | Theorems.Thm_GlobalTheory_UnitVectorStabEq_hform_eq
-- name    : GlobalTheory.UnitVectorStabEq.hform_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:19.919365+00:00
-- url     : https://prove2.me/theorems/c2d4794b-9400-424e-89fe-4f43b5e1307f
-- title:
--   Unit Vector Stab Eq: hform eq
-- statement:
--   The Unit Vector Stab Eq construction uses the hform eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/StabLatInfStabVec.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/StabLatInfStabVec.lean#L15-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open GlobalTheory GlobalTheory.UnitVectorStabEq
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.UnitVectorStabEq.hform_eq (s : A →+* A) (J : Matrix n n A) (y z : n → A) :
    Formalism.UG.hform s J y z = (s ∘ y) ⬝ᵥ (J *ᵥ z) := by sorry
