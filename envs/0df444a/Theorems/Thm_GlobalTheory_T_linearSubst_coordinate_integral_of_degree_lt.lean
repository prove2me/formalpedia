-- Prove2me | Theorems.Thm_GlobalTheory_T_linearSubst_coordinate_integral_of_degree_lt
-- name    : GlobalTheory.T.linearSubst_coordinate_integral_of_degree_lt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:01:53.084423+00:00
-- url     : https://prove2.me/theorems/b5450b27-933b-410d-be35-55ec969cf442
-- title:
--   T: linear Subst coordinate integral of degree lt
-- statement:
--   The T construction uses the linear Subst coordinate integral of degree lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LinearSubstCoordinateIntegralOfDegreeLtStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LinearSubstCoordinateIntegralOfDegreeLtStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LinearSubstCoordinateIntegralOfDegreeLt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LinearSubstCoordinateIntegralOfDegreeLtStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.linearSubst_coordinate_integral_of_degree_lt : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (e : Fin N → I → C), (∀ j x, V.Ge 0 (e j x)) → ∀ μ : Fin N →₀ ℕ, μ.degree < V.l → ∀ c, V.Ge 0 (MvPowerSeries.coeff μ (linPull e (t c))) := by sorry
