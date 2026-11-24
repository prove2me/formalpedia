-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_SqfCrt_mem_prod_smul_of_coprime
-- name    : GlobalTheory.RowLev.SqfCrt.mem_prod_smul_of_coprime
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:34:20.314902+00:00
-- url     : https://prove2.me/theorems/485a5bee-24e4-4488-aba7-e1528082d825
-- title:
--   Sqf Crt: mem prod smul of coprime
-- statement:
--   The Sqf Crt construction uses the mem prod smul of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsProdLeOfIsRadical.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsProdLeOfIsRadical.lean#L21-L30

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsProdLeOfIsRadical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev GlobalTheory.RowLev.SqfCrt

theorem GlobalTheory.RowLev.SqfCrt.mem_prod_smul_of_coprime {S M ι : Type*} [CommRing S] [AddCommGroup M] [Module S M] (N : Submodule S M)
    (J : ι → Ideal S) (hJ : ∀ i j, i ≠ j → IsCoprime (J i) (J j)) {y : M} (hy : y ∈ N) (T : Finset ι)
    (h : ∀ i ∈ T, y ∈ J i • N) : y ∈ (∏ i ∈ T, J i) • N := by sorry
