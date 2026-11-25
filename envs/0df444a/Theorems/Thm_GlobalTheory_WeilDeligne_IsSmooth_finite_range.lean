-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_IsSmooth_finite_range
-- name    : GlobalTheory.WeilDeligne.IsSmooth.finite_range
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:51:29.211479+00:00
-- url     : https://prove2.me/theorems/d0649b91-3c6e-59e2-9dd1-69f342007226
-- title:
--   Is Smooth: finite range
-- statement:
--   The Is Smooth construction uses the finite range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MonodromyZeroOfWeilDeligneRepClassIff.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MonodromyZeroOfWeilDeligneRepClassIff.lean#L49-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable [IsAlgClosure E Ω]

theorem GlobalTheory.WeilDeligne.IsSmooth.finite_range {h : IsPlaceOver A w} {M : Type*} [Monoid M] {f : Weil h →* M}
    (hf : IsSmooth f) : (Set.range fun σ : Ine (F := E) A => f (ineIncl h σ)).Finite := by sorry
