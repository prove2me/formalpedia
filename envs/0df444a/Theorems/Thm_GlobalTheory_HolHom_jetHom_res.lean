-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_jetHom_res
-- name    : GlobalTheory.HolHom.jetHom_res
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:38:26.717362+00:00
-- url     : https://prove2.me/theorems/86d44451-8480-4a2e-94ed-38dfd27f937b
-- title:
--   Hol Hom: jet Hom res
-- statement:
--   The Hol Hom construction uses the jet Hom res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L301-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L301-L309

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

theorem GlobalTheory.HolHom.jetHom_res {c : V → (Sp ℂ ⟶ X)} {z : V} (h : HolAt c z) (w : V) {U U' : X.Opens} (hle : U' ≤ U)
    (hU : ⊤ ≤ c z ⁻¹ᵁ U) (hU' : ⊤ ≤ c z ⁻¹ᵁ U') (f : Γ(X, U)) :
    jetHom h w U' hU' ((X.presheaf.map (homOfLE hle).op).hom f) = jetHom h w U hU f := by sorry
