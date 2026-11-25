-- Prove2me | Theorems.Thm_GlobalTheory_InertiaMovesRoot_exists_mem_Ine_apply_ne
-- name    : GlobalTheory.InertiaMovesRoot.exists_mem_Ine_apply_ne
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:59:03.037319+00:00
-- url     : https://prove2.me/theorems/934240a3-e826-5a1b-8243-9e2c8dcbdd93
-- title:
--   Inertia Moves Root: exists mem Ine apply ne
-- statement:
--   The Inertia Moves Root construction uses the exists mem Ine apply ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCongOfCongOnFixed.lean#L212-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCongOfCongOnFixed.lean#L212-L240

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

theorem GlobalTheory.InertiaMovesRoot.exists_mem_Ine_apply_ne : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (l : ℕ), l.Prime → ∀ (ϖ : 𝓞 E), ϖ ∈ w.asIdeal → ϖ ∉ w.asIdeal ^ 2 → ∀ x : Ω,
    x ^ l = algebraMap E Ω (ϖ : E) → ∃ σ ∈ Ine (F := E) A, σ x ≠ x := by sorry
