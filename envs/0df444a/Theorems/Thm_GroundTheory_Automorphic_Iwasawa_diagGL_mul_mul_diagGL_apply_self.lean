-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Iwasawa_diagGL_mul_mul_diagGL_apply_self
-- name    : GroundTheory.Automorphic.Iwasawa.diagGL_mul_mul_diagGL_apply_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:11.877624+00:00
-- url     : https://prove2.me/theorems/5d5e6df9-cbe2-435c-bea6-3a392c3ebcf5
-- title:
--   Iwasawa: diag GL mul mul diag GL apply self
-- statement:
--   The Iwasawa construction uses the diag GL mul mul diag GL apply self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L103-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L103-L109

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

theorem GroundTheory.Automorphic.Iwasawa.diagGL_mul_mul_diagGL_apply_self {u : GL (Fin n) F} (hu : u ∈ unipotent F n)
    (a c : Fin n → Fˣ) (i : Fin n) :
    (diagGL F n a * u * diagGL F n c : GL (Fin n) F) i i = a i * c i := by sorry
