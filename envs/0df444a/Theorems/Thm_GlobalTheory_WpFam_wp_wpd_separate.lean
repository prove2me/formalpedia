-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_wp_wpd_separate
-- name    : GlobalTheory.WpFam.wp_wpd_separate
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:57:39.551862+00:00
-- url     : https://prove2.me/theorems/fb341c77-b2db-4e1f-b575-bd29c26d0a35
-- title:
--   Wp Fam: wp wpd separate
-- statement:
--   The Wp Fam construction uses the wp wpd separate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqOfWeierstrassPDerivWeierstrassPTorsionEq.lean#L10-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqOfWeierstrassPDerivWeierstrassPTorsionEq.lean#L10-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointOfLatticeTauLatticeMembershipStatement
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EllipticOnePole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqOfWeierstrassPDerivWeierstrassPTorsionEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam

theorem GlobalTheory.WpFam.wp_wpd_separate : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 →
    wp N x τ = wp N y τ → wpd N x τ = wpd N y τ → x = y := by sorry
