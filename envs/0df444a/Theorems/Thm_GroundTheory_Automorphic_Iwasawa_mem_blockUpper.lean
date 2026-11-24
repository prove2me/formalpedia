-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Iwasawa_mem_blockUpper
-- name    : GroundTheory.Automorphic.Iwasawa.mem_blockUpper
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:42.192314+00:00
-- url     : https://prove2.me/theorems/f118284f-5357-42f9-9051-a351cdfaf12b
-- title:
--   Iwasawa: mem block Upper
-- statement:
--   The Iwasawa construction uses the mem block Upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L32-L34

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Matrix Filter
open scoped Pointwise
open GroundTheory.Automorphic.Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)

theorem GroundTheory.Automorphic.Iwasawa.mem_blockUpper {α : Type*} [LinearOrder α] {β : Fin n → α} {g : GL (Fin n) F} :
    g ∈ blockUpper F n β ↔ (g : Matrix (Fin n) (Fin n) F).BlockTriangular β := by sorry
