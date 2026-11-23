-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_conj_eq_self_iff
-- name    : GroundTheory.Automorphic.conj_eq_self_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:51.846855+00:00
-- url     : https://prove2.me/theorems/e3a91fc8-8fe1-4ad9-a4b5-77fd692db8ec
-- title:
--   Automorphic: conj eq self iff
-- statement:
--   The Automorphic construction uses the conj eq self iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L37-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L37-L60

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

theorem GroundTheory.Automorphic.conj_eq_self_iff [Algebra.IsSeparable F E] {x : E} :
    conj F E x = x ↔ x ∈ Set.range (algebraMap F E) := by sorry
