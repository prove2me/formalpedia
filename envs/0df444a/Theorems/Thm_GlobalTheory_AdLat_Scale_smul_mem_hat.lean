-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_Scale_smul_mem_hat
-- name    : GlobalTheory.AdLat.Scale.smul_mem_hat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:53:54.145854+00:00
-- url     : https://prove2.me/theorems/4b983e02-3152-4bc6-97b2-42e5e018041b
-- title:
--   Scale: smul mem hat
-- statement:
--   The Scale construction uses the smul mem hat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ZeroMemLatOf.lean#L15-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ZeroMemLatOf.lean#L15-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ZeroMemLatOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Scale
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem GlobalTheory.AdLat.Scale.smul_mem_hat {L L' : Set (Fin n → E)} {a : E}
    (h : ∀ x ∈ L, a • x ∈ L')
    {z : Fin n → _root_.GlobalTheory.AdLat.RA F E} (hz : z ∈ _root_.GlobalTheory.AdLat.hat F L) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a : _root_.GlobalTheory.AdLat.RA F E) • z ∈
      _root_.GlobalTheory.AdLat.hat F L' := by sorry
