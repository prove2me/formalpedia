-- Prove2me | Theorems.Thm_GlobalTheory_MuTowerInj_injective_of_card
-- name    : GlobalTheory.MuTowerInj.injective_of_card
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:28:05.389733+00:00
-- url     : https://prove2.me/theorems/12b83b1e-c439-4acb-bfc0-0a9942b64642
-- title:
--   Mu Tower Inj: injective of card
-- statement:
--   The Mu Tower Inj construction uses the injective of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MuCocycleCoboundaryLift.lean#L92-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MuCocycleCoboundaryLift.lean#L92-L118

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MuCocycleCoboundaryLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory GlobalTheory.MuTowerInj
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {R₁ R₂ R₃ M₁ M₂ M₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃]
  [DiscreteTopology M₁] [DiscreteTopology M₂] [DiscreteTopology M₃]

theorem GlobalTheory.MuTowerInj.injective_of_card {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Finite A] [Finite B] [Finite C] (f : A →+ B) (g : B →+ C) (h : g.ker ≤ f.range)
    (hc : Nat.card B = Nat.card A * Nat.card C) : Function.Injective f := by sorry
