-- Prove2me | Theorems.Thm_GlobalTheory_HeckeIdealValue_onId_prime
-- name    : GlobalTheory.HeckeIdealValue.onId_prime
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:03:16.109801+00:00
-- url     : https://prove2.me/theorems/70cf3004-f846-495c-a0ca-444283cfc663
-- title:
--   Hecke Ideal Value: on Id prime
-- statement:
--   The Hecke Ideal Value construction uses the on Id prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeCharOnIdMulSqrtAbsNormInvMemSubring.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeCharOnIdMulSqrtAbsNormInvMemSubring.lean#L30-L35

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

theorem GlobalTheory.HeckeIdealValue.onId_prime (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    χ.onId ((v.asIdeal : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) = χ.val v := by sorry
