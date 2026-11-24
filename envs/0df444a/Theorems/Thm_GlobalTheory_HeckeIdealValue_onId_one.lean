-- Prove2me | Theorems.Thm_GlobalTheory_HeckeIdealValue_onId_one
-- name    : GlobalTheory.HeckeIdealValue.onId_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:03:03.643851+00:00
-- url     : https://prove2.me/theorems/f9c2976d-5edb-4295-a772-a73b70f6e8d8
-- title:
--   Hecke Ideal Value: on Id one
-- statement:
--   The Hecke Ideal Value construction uses the on Id one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeCharOnIdMulSqrtAbsNormInvMemSubring.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeCharOnIdMulSqrtAbsNormInvMemSubring.lean#L26-L28

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

theorem GlobalTheory.HeckeIdealValue.onId_one (χ : HChar L) : χ.onId (1 : FractionalIdeal (𝓞 L)⁰ L) = 1 := by sorry
