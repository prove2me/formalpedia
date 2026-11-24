-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_eq_of_fderiv_eq
-- name    : GlobalTheory.HolHom.eq_of_fderiv_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:49.022623+00:00
-- url     : https://prove2.me/theorems/f59ac768-3104-4676-bd7e-6343ca04e167
-- title:
--   Hol Hom: eq of fderiv eq
-- statement:
--   The Hol Hom construction uses the eq of fderiv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L422-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L422-L462

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {S : Scheme.{0}}
variable {G : Over S} [GrpObj G]
variable {y : Sp ℂ ⟶ S}

theorem GlobalTheory.HolHom.eq_of_fderiv_eq {e e' : V → (Over.mk y ⟶ G)} (he : ∀ z w, e (z + w) = e z * e w)
    (he' : ∀ z w, e' (z + w) = e' z * e' w) (hol : IsHolTo Set.univ (fun z => (e z).left))
    (hol' : IsHolTo Set.univ (fun z => (e' z).left))
    (hd : ∀ U : G.left.Opens, ⊤ ≤ (e 0).left ⁻¹ᵁ U → ∀ f : Γ(G.left, U),
      fderiv ℂ (fun z => valAt' (e z).left U f) 0 = fderiv ℂ (fun z => valAt' (e' z).left U f) 0) : e = e' := by sorry
