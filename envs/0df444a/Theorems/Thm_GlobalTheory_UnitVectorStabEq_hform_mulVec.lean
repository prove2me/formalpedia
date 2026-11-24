-- Prove2me | Theorems.Thm_GlobalTheory_UnitVectorStabEq_hform_mulVec
-- name    : GlobalTheory.UnitVectorStabEq.hform_mulVec
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:38:50.664798+00:00
-- url     : https://prove2.me/theorems/fb922b27-ec01-4ee7-9b9d-66f456768264
-- title:
--   Unit Vector Stab Eq: hform mul Vec
-- statement:
--   The Unit Vector Stab Eq construction uses the hform mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/StabLatInfStabVec.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/StabLatInfStabVec.lean#L19-L25

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

theorem GlobalTheory.UnitVectorStabEq.hform_mulVec (s : A →+* A) (J g : Matrix n n A) (y z : n → A) :
    Formalism.UG.hform s J (g *ᵥ y) (g *ᵥ z) = Formalism.UG.hform s (Formalism.UG.cT s g * J * g) y z := by sorry
