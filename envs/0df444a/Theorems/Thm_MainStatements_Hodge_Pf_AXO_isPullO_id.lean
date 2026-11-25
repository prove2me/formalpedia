-- Prove2me | Theorems.Thm_MainStatements_Hodge_Pf_AXO_isPullO_id
-- name    : MainStatements.Hodge.Pf.AXO.isPullO_id
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:15.330984+00:00
-- url     : https://prove2.me/theorems/08648682-a5bc-4a77-b142-84ff0ff3c8bb
-- title:
--   AXO: is Pull O id
-- statement:
--   The AXO construction uses the is Pull O id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/AbelianDeRham/AbelianPullbackLattices/CompositeRestrictionPullInjective.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/AbelianDeRham/AbelianPullbackLattices/CompositeRestrictionPullInjective.lean#L96-L98

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianPullbackLattices_CompositeRestrictionPullInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open MainStatements MainStatements.Hodge MainStatements.Hodge.Pf MainStatements.Hodge.Pf.AXO
variable {R : Type} [CommRing R]

theorem MainStatements.Hodge.Pf.AXO.isPullO_id {X : Scheme.{0}} (s : X ⟶ Sp R) (φ : X ⟶ X) (hφ : φ = 𝟙 X)
    (h : φ ≫ s = s ≫ spMap (RingHom.id R)) (c : HO1 s) : IsPullO h c c := by sorry
