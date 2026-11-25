-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_gal_fix_cyclotomicLayer_cycloChar_ne_one
-- name    : GroundTheory.PAdicHodge.exists_gal_fix_cyclotomicLayer_cycloChar_ne_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:10:23.405987+00:00
-- url     : https://prove2.me/theorems/c5ea4d23-93bb-5e5f-9e9b-b8fb40c115fc
-- title:
--   PAdic Hodge: exists gal fix cyclotomic Layer cyclo Char ne one
-- statement:
--   The PAdic Hodge construction uses the exists gal fix cyclotomic Layer cyclo Char ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExistsGalFixCyclotomicLayerCycloCharNeOne.lean#L164-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExistsGalFixCyclotomicLayerCycloCharNeOne.lean#L164-L194

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_ExistsGalFixCyclotomicLayerCycloCharNeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField UniformSpace
variable {p : ℕ} [hp : Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable [FiniteDimensional ℚ_[p] K]

theorem GroundTheory.PAdicHodge.exists_gal_fix_cyclotomicLayer_cycloChar_ne_one (n : ℕ) :
    ∃ σ : Gal(PadicAlgCl p/K), (∀ y ∈ cyclotomicLayer K n, σ y = y) ∧ cycloChar K σ ≠ 1 := by sorry
