-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_eq_of_forall_fderiv_eq
-- name    : GlobalTheory.HolHom.eq_of_forall_fderiv_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:38.824776+00:00
-- url     : https://prove2.me/theorems/1fdfa7b6-e92f-4cd8-a7fa-b6d985946afb
-- title:
--   Hol Hom: eq of forall fderiv eq
-- statement:
--   The Hol Hom construction uses the eq of forall fderiv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L478-L486
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L478-L486

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

theorem GlobalTheory.HolHom.eq_of_forall_fderiv_eq {y : Sp ℂ ⟶ S} {e' : (Fin g → ℂ) → (Over.mk y ⟶ G)}
    (hol' : HolAt (fun z => (e' z).left) 0)
    (hdiff : ∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left →
      ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) {w w' : Fin g → ℂ}
    (h : ∀ U : G.left.Opens, ⊤ ≤ (e' 0).left ⁻¹ᵁ U → ∀ f : Γ(G.left, U),
      fderiv ℂ (fun z => valAt' (e' z).left U f) 0 w = fderiv ℂ (fun z => valAt' (e' z).left U f) 0 w') : w = w' := by sorry
