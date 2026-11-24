-- Prove2me | Theorems.Thm_GlobalTheory_T_formallyUnramified_mul_invertible_integer
-- name    : GlobalTheory.T.formallyUnramified_mul_invertible_integer
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:41:21.218741+00:00
-- url     : https://prove2.me/theorems/3dd774b4-e6ab-401e-bb08-d064728fb648
-- title:
--   T: formally Unramified mul invertible integer
-- statement:
--   The T construction uses the formally Unramified mul invertible integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FormallyUnramifiedMulInvertibleIntegerStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FormallyUnramifiedMulInvertibleIntegerStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FormallyUnramifiedMulInvertibleInteger
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FormallyUnramifiedMulInvertibleIntegerStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.T.formallyUnramified_mul_invertible_integer : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ), IsUnit (n : Γ(S, ⊤)) → FormallyUnramified (mulA G n).left := by sorry
