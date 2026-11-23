-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_isometric_prod_restrict
-- name    : GroundTheory.Automorphic.HermitianForm.isometric_prod_restrict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:00.969556+00:00
-- url     : https://prove2.me/theorems/06fb3447-6878-42df-83c9-19e38391a630
-- title:
--   Hermitian Form: isometric prod restrict
-- statement:
--   The Hermitian Form construction uses the isometric prod restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L275-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L275-L282

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
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
variable {V V' V'' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  [AddCommGroup V''] [Module E V'']
open GroundTheory.Automorphic.HermitianForm

theorem GroundTheory.Automorphic.HermitianForm.isometric_prod_restrict (h : HermitianForm F E V) (W W' : Submodule E V)
    (hW : h.IsOrthoCompl W W') :
    Isometric ((h.restrict W W' hW).prod (h.restrict W' W hW.symm)) h := by sorry
