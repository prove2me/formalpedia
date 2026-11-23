-- Prove2me | Theorems.Thm_Neutral_B1_abRestrict_mk
-- name    : Neutral.B1.abRestrict_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:07.705316+00:00
-- url     : https://prove2.me/theorems/e42583e8-0774-44e5-9a19-7b402e5e9c74
-- title:
--   B1: ab Restrict mk
-- statement:
--   The B1 construction uses the ab Restrict mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean#L51-L56

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Topology
open Neutral Neutral.B1
variable (F : Type*) [Field F]

theorem Neutral.B1.abRestrict_mk (L : IntermediateField F (AlgebraicClosure F)) (h : IsFiniteAbelian F L)
    (g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    haveI := h.isGalois
    abRestrict F L h (toAb F g) = AlgEquiv.restrictNormalHom L g := by sorry
