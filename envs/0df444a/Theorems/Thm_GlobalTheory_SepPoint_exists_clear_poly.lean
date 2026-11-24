-- Prove2me | Theorems.Thm_GlobalTheory_SepPoint_exists_clear_poly
-- name    : GlobalTheory.SepPoint.exists_clear_poly
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:53:02.140062+00:00
-- url     : https://prove2.me/theorems/9a170217-535c-419d-931e-baf439fd411a
-- title:
--   Sep Point: exists clear poly
-- statement:
--   The Sep Point construction uses the exists clear poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimitiveElementSeparabilityCertificate.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimitiveElementSeparabilityCertificate.lean#L9-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegrallyClosedAdjoin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveElementSeparabilityCertificate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin
open GlobalTheory GlobalTheory.SepPoint

theorem GlobalTheory.SepPoint.exists_clear_poly {k F : Type} [Field k] [Field F] [Algebra k F] (s : Set F)
    (p : (IntermediateField.adjoin k s)[X]) :
    ∃ q : (Algebra.adjoin k s)[X], ∃ b : Algebra.adjoin k s, b ≠ 0 ∧
      q.map (algebraMap (Algebra.adjoin k s) (IntermediateField.adjoin k s)) =
        C (algebraMap (Algebra.adjoin k s) (IntermediateField.adjoin k s) b) * p := by sorry
