-- Prove2me | Theorems.Thm_GlobalTheory_InertiaMovesRoot_mem_Ine_of_cong
-- name    : GlobalTheory.InertiaMovesRoot.mem_Ine_of_cong
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:58:50.703885+00:00
-- url     : https://prove2.me/theorems/c6f964c0-b353-5e82-8636-6951c337a85a
-- title:
--   Inertia Moves Root: mem Ine of cong
-- statement:
--   The Inertia Moves Root construction uses the mem Ine of cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCongOfCongOnFixed.lean#L146-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCongOfCongOnFixed.lean#L146-L169

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

theorem GlobalTheory.InertiaMovesRoot.mem_Ine_of_cong {σ : Ω ≃ₐ[E] Ω}
    (hσ : ∀ b : IntCl E Ω, σ • b - b ∈ primeBelow (F := E) A) : σ ∈ Ine (F := E) A := by sorry
