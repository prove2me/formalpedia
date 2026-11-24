-- Prove2me | Theorems.Thm_GlobalTheory_AffineThickening_exists_ker_app_eq_map
-- name    : GlobalTheory.AffineThickening.exists_ker_app_eq_map
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:58:12.651625+00:00
-- url     : https://prove2.me/theorems/2a9d3327-f20a-442b-9869-e303711028d8
-- title:
--   Affine Thickening: exists ker app eq map
-- statement:
--   The Affine Thickening construction uses the exists ker app eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L308-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L308-L321

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory GlobalTheory.AffineThickening
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y)
variable {i}

theorem GlobalTheory.AffineThickening.exists_ker_app_eq_map {A C : CommRingCat.{u}} {β : A ⟶ C}
    (hβ : Function.Surjective β) {f : Y ⟶ Spec A} {i : Z ⟶ Y} {f' : Z ⟶ Spec C}
    (h : IsPullback i f' f (Spec.map β)) {U : Y.Opens} (hU : IsAffineOpen U) :
    ∃ α : A →+* Γ(Y, U), RingHom.ker (i.app U).hom = (RingHom.ker β.hom).map α := by sorry
