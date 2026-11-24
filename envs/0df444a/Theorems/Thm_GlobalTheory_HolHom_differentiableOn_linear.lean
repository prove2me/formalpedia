-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_differentiableOn_linear
-- name    : GlobalTheory.HolHom.differentiableOn_linear
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:36:09.653792+00:00
-- url     : https://prove2.me/theorems/743481bd-0279-41c0-88a5-4ec18a31e5a0
-- title:
--   Hol Hom: differentiable On linear
-- statement:
--   The Hol Hom construction uses the differentiable On linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L543-L615
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L543-L615

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

theorem GlobalTheory.HolHom.differentiableOn_linear {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    [FiniteDimensional ℂ V] {B : Set P} {y : P → (Sp ℂ ⟶ S)} {e : ∀ b, V → (Over.mk (y b) ⟶ G)}
    {e' : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)}
    (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : P × V => (e bz.1 bz.2).left))
    (hol' : IsHolTo (B ×ˢ Set.univ) (fun bz : P × (Fin g → ℂ) => (e' bz.1 bz.2).left))
    (hdiff : ∀ b ∈ B, ∀ v : epsPt (y b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' b 0).left →
      ∃! w, IsDerivAt0 (fun z => (e' b z).left) w v.left)
    {h : P → V →ₗ[ℂ] (Fin g → ℂ)} (hh : ∀ b ∈ B, ∀ z, e b z = e' b (h b z)) :
    DifferentiableOn ℂ (fun b => LinearMap.toContinuousLinearMap (h b)) B := by sorry
