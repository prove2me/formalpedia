-- Prove2me | Theorems.Thm_Neutral_B1_mem_perpCond
-- name    : Neutral.B1.mem_perpCond
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:04:04.49817+00:00
-- url     : https://prove2.me/theorems/e87a22bb-0f28-52f5-94fc-e7b8bde76736
-- title:
--   B1: mem perp Cond
-- statement:
--   The B1 construction uses the mem perp Cond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Duality.lean#L768-L772
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Duality.lean#L768-L772

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
open Neutral Neutral.B1
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M]
variable {D : Type*} [Group D] [TopologicalSpace D]
  (χ : Γ →* Rˣ) (rho : Representation R Γ M) (φ : D →* Γ)

theorem Neutral.B1.mem_perpCond {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
    (phi : ∀ i, D i →* Γ) (hrho : ∀ i, ContAction (rho.comp (phi i)))
    (L : ∀ i, Submodule R (H1 (rho.comp (phi i)))) (i : I) (y : H1 ((twDual χ rho).comp (phi i))) :
    y ∈ perpCond χ rho phi hrho L i ↔ ∀ x ∈ L i, cupH1H1TwistedDual χ rho (phi i) (hrho i) y x = 0 := by sorry
