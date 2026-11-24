-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Iwasawa_diagGL_mul_mul_inv_mem_unipotent
-- name    : GroundTheory.Automorphic.Iwasawa.diagGL_mul_mul_inv_mem_unipotent
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:13:18.547726+00:00
-- url     : https://prove2.me/theorems/acc12761-986f-49f0-a2f5-151609e77245
-- title:
--   Iwasawa: diag GL mul mul inv mem unipotent
-- statement:
--   The Iwasawa construction uses the diag GL mul mul inv mem unipotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L111-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L111-L116

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

theorem GroundTheory.Automorphic.Iwasawa.diagGL_mul_mul_inv_mem_unipotent {u : GL (Fin n) F} (hu : u ∈ unipotent F n)
    (d : Fin n → Fˣ) : diagGL F n d * u * (diagGL F n d)⁻¹ ∈ unipotent F n := by sorry
