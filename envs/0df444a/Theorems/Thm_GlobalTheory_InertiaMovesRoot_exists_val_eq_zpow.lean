-- Prove2me | Theorems.Thm_GlobalTheory_InertiaMovesRoot_exists_val_eq_zpow
-- name    : GlobalTheory.InertiaMovesRoot.exists_val_eq_zpow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:58:48.206267+00:00
-- url     : https://prove2.me/theorems/30420daa-9770-5258-b152-0b9776f574ff
-- title:
--   Inertia Moves Root: exists val eq zpow
-- statement:
--   The Inertia Moves Root construction uses the exists val eq zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCongOfCongOnFixed.lean#L16-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCongOfCongOnFixed.lean#L16-L46

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

theorem GlobalTheory.InertiaMovesRoot.exists_val_eq_zpow (h : IsPlaceOver A w) {ϖ : 𝓞 E} (h1 : ϖ ∈ w.asIdeal)
    (h2 : ϖ ∉ w.asIdeal ^ 2) {a : E} (ha : a ≠ 0) :
    ∃ m : ℤ, A.valuation (algebraMap E Ω a) = A.valuation (algebraMap E Ω (ϖ : E)) ^ m := by sorry
