-- Prove2me | Theorems.Thm_GlobalTheory_T_hom_ext_of_agree_on_fibreDense_open_smooth
-- name    : GlobalTheory.T.hom_ext_of_agree_on_fibreDense_open_smooth
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:47:44.736595+00:00
-- url     : https://prove2.me/theorems/e9badf67-d036-4c1d-a0b8-183c0dad9203
-- title:
--   T: hom ext of agree on fibre Dense open smooth
-- statement:
--   The T construction uses the hom ext of agree on fibre Dense open smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomExtOfAgreeOnFibreDenseOpenSmoothStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomExtOfAgreeOnFibreDenseOpenSmoothStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomExtOfAgreeOnFibreDenseOpenSmooth
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomExtOfAgreeOnFibreDenseOpenSmoothStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hom_ext_of_agree_on_fibreDense_open_smooth : ∀ (X T Y : Scheme.{0}) (p : X ⟶ T) [Smooth p] (q : Y ⟶ T) [IsSeparated q] (W : X.Opens), (∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) → ∀ f g : X ⟶ Y, f ≫ q = g ≫ q → W.ι ≫ f = W.ι ≫ g → f = g := by sorry
