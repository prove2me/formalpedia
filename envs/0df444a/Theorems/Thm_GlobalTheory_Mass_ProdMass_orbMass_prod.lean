-- Prove2me | Theorems.Thm_GlobalTheory_Mass_ProdMass_orbMass_prod
-- name    : GlobalTheory.Mass.ProdMass.orbMass_prod
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:09:50.701356+00:00
-- url     : https://prove2.me/theorems/0344d753-f861-5cf5-b235-e71eb70b9bf8
-- title:
--   Prod Mass: orb Mass prod
-- statement:
--   The Prod Mass construction uses the orb Mass prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitStabilizerMassProdEqMul.lean#L99-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitStabilizerMassProdEqMul.lean#L99-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitStabilizerMassProdEqMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.ProdMass
variable {Γ G G' α β : Type} [Group Γ] [Group G] [Group G'] [MulAction G α] [MulAction G' β]
  [MulAction Γ (α × β)] (φ : Γ ≃* G × G')
  (hφ : ∀ (γ : Γ) (p : α × β), γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2))

theorem GlobalTheory.Mass.ProdMass.orbMass_prod : ∀ (Γ G G' α β : Type) [Group Γ] [Group G] [Group G'] [MulAction G α]
    [MulAction G' β] [MulAction Γ (α × β)] (φ : Γ ≃* G × G') (X : Set α) (Y : Set β),
    (∀ (γ : Γ) (p : α × β), γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2)) → Stable G X → Stable G' Y →
    (∀ x ∈ X, Finite (MulAction.stabilizer G x)) → (∀ y ∈ Y, Finite (MulAction.stabilizer G' y)) →
    orbMass Γ (X ×ˢ Y) = orbMass G X * orbMass G' Y := by sorry
