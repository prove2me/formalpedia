-- Prove2me | Theorems.Thm_GlobalTheory_InertiaMovesRoot_cong_on_adjoin
-- name    : GlobalTheory.InertiaMovesRoot.cong_on_adjoin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:58:44.926693+00:00
-- url     : https://prove2.me/theorems/77bb549b-3259-5215-8d28-3ab2968f1996
-- title:
--   Inertia Moves Root: cong on adjoin
-- statement:
--   The Inertia Moves Root construction uses the cong on adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCongOfCongOnFixed.lean#L64-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCongOfCongOnFixed.lean#L64-L144

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCongOfCongOnFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne Pointwise
open GlobalTheory GlobalTheory.InertiaMovesRoot
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem GlobalTheory.InertiaMovesRoot.cong_on_adjoin (h : IsPlaceOver A w) {l : ℕ} (hl : 2 ≤ l) {ϖ : 𝓞 E} (h1 : ϖ ∈ w.asIdeal)
    (h2 : ϖ ∉ w.asIdeal ^ 2) {x : Ω} (hx : x ^ l = algebraMap E Ω (ϖ : E)) :
    x ∉ (⊥ : IntermediateField E Ω) ∧ ∀ (g : Ω ≃ₐ[E] Ω) (b : Ω),
      b ∈ IntermediateField.adjoin E {x} → A.valuation b ≤ 1 → A.valuation (g b - b) < 1 := by sorry
