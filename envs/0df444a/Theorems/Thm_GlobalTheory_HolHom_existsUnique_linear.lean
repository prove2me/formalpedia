-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_existsUnique_linear
-- name    : GlobalTheory.HolHom.existsUnique_linear
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:25.505961+00:00
-- url     : https://prove2.me/theorems/0f99efe9-aef9-4c9b-a588-18b56b0f8d11
-- title:
--   Hol Hom: exists Unique linear
-- statement:
--   The Hol Hom construction uses the exists Unique linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L488-L529
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L488-L529

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolHom
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {S : Scheme.{0}} {G : Over S} {g : ℕ}

theorem GlobalTheory.HolHom.existsUnique_linear [FiniteDimensional ℂ V] [GrpObj G] {y : Sp ℂ ⟶ S} {e : V → (Over.mk y ⟶ G)}
    {e' : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : ∀ z w, e (z + w) = e z * e w)
    (he' : ∀ z w, e' (z + w) = e' z * e' w) (hol : IsHolTo Set.univ (fun z => (e z).left))
    (hol' : IsHolTo Set.univ (fun z => (e' z).left))
    (hdiff : ∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left →
      ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) :
    ∃! h : V →ₗ[ℂ] (Fin g → ℂ), ∀ z, e z = e' (h z) := by sorry
