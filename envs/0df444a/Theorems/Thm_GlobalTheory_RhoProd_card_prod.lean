-- Prove2me | Theorems.Thm_GlobalTheory_RhoProd_card_prod
-- name    : GlobalTheory.RhoProd.card_prod
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:22:53.786519+00:00
-- url     : https://prove2.me/theorems/ef57c764-ddef-49eb-b11c-90db367112fe
-- title:
--   Rho Prod: card prod
-- statement:
--   The Rho Prod construction uses the card prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RhoProdFiniteAlgebraWithInvolution.lean#L15-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RhoProdFiniteAlgebraWithInvolution.lean#L15-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RhoProdFiniteAlgebraWithInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
open GlobalTheory GlobalTheory.RhoProd

theorem GlobalTheory.RhoProd.card_prod {G G₁ G₂ : Type} [Group G] [Group G₁] [Group G₂]
    (H : Subgroup G) (H₁ : Subgroup G₁) (H₂ : Subgroup G₂) (e : G ≃* G₁ × G₂)
    (he : ∀ g, g ∈ H ↔ (e g).1 ∈ H₁ ∧ (e g).2 ∈ H₂)
    (P : G → Prop) (P₁ : G₁ → Prop) (P₂ : G₂ → Prop)
    (hP : ∀ g, P g ↔ P₁ (e g).1 ∧ P₂ (e g).2)
    (h₁ : ∀ g h, h ∈ H₁ → (P₁ (g * h) ↔ P₁ g)) (h₂ : ∀ g h, h ∈ H₂ → (P₂ (g * h) ↔ P₂ g)) :
    Nat.card {k : G ⧸ H // P (Quotient.out k)} =
      Nat.card {k : G₁ ⧸ H₁ // P₁ (Quotient.out k)} * Nat.card {k : G₂ ⧸ H₂ // P₂ (Quotient.out k)} := by sorry
