-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_exists_isometric_prod_ofUnit
-- name    : GroundTheory.Automorphic.HermitianForm.exists_isometric_prod_ofUnit
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:24.171005+00:00
-- url     : https://prove2.me/theorems/a399e242-3610-400e-83d9-5d5fa10410bb
-- title:
--   Hermitian Form: exists isometric prod of Unit
-- statement:
--   The Hermitian Form construction uses the exists isometric prod of Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L47-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L47-L67

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
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
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V₁] [Module E V₁]
  [AddCommGroup V₂] [Module E V₂]
open GroundTheory.Automorphic.HermitianForm

theorem GroundTheory.Automorphic.HermitianForm.exists_isometric_prod_ofUnit (h : HermitianForm F E V) {v : V} {a : Fˣ}
    (hv : h.toSesq v v = algebraMap F E a) :
    ∃ (W : Submodule E V) (h₀ : HermitianForm F E W),
      Isometric ((ofUnit (E := E) a).prod h₀) h ∧
        (FiniteDimensional E V → finrank E W + 1 = finrank E V) := by sorry
