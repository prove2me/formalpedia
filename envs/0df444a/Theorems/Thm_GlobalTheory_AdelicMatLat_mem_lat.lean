-- Prove2me | Theorems.Thm_GlobalTheory_AdelicMatLat_mem_lat
-- name    : GlobalTheory.AdelicMatLat.mem_lat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:56:00.442985+00:00
-- url     : https://prove2.me/theorems/af15a39f-0a22-4317-a3f7-e8f5fa0f9412
-- title:
--   Adelic Mat Lat: mem lat
-- statement:
--   The Adelic Mat Lat construction uses the mem lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsLatticeAdelicMatrixIntegralTranslate.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsLatticeAdelicMatrixIntegralTranslate.lean#L77-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsLatticeAdelicMatrixIntegralTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.AdelicMatLat
variable (E : Type) [Field E] [NumberField E]
variable {E} {n : ℕ}

theorem GlobalTheory.AdelicMatLat.mem_lat {β : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)} {x : Fin n → E} :
    x ∈ lat β ↔
      ∀ j, ∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β k j ∈ intAdeles E := by sorry
