-- Prove2me | Theorems.Thm_GlobalTheory_HeckeIdealValue_finite_supp
-- name    : GlobalTheory.HeckeIdealValue.finite_supp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:03:08.126886+00:00
-- url     : https://prove2.me/theorems/c561a7b0-3a4b-4eb6-b851-8a6479dcee98
-- title:
--   Hecke Ideal Value: finite supp
-- statement:
--   The Hecke Ideal Value construction uses the finite supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeCharOnIdMulSqrtAbsNormInvMemSubring.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeCharOnIdMulSqrtAbsNormInvMemSubring.lean#L14-L17

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HeckeCharOnIdMulSqrtAbsNormInvMemSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.HeckeIdealValue
open Formalism.L2.Host
variable {L : Type} [Field L] [NumberField L]

theorem GlobalTheory.HeckeIdealValue.finite_supp (χ : HChar L) (J : FractionalIdeal (𝓞 L)⁰ L) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) => χ.val v ^ FractionalIdeal.count L v J).Finite := by sorry
