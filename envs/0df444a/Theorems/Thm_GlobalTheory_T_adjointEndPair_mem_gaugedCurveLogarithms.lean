-- Prove2me | Theorems.Thm_GlobalTheory_T_adjointEndPair_mem_gaugedCurveLogarithms
-- name    : GlobalTheory.T.adjointEndPair_mem_gaugedCurveLogarithms
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-27T05:21:58.606499+00:00
-- url     : https://prove2.me/theorems/59e5052e-e7e4-53a1-b5e4-3d65bb6ec799
-- title:
--   T: adjoint End Pair mem gauged Curve Logarithms
-- statement:
--   The T construction uses the adjoint End Pair mem gauged Curve Logarithms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AdjointEndPairMemGaugedCurveLogarithmsStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AdjointEndPairMemGaugedCurveLogarithmsStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithmsStatement
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.adjointEndPair_mem_gaugedCurveLogarithms : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (M M' : Matrix κ κ C) (s : JJ I g → C), IsEnd X V M M' → (∀ q, V.Ge 0 (s q)) → (∀ q, M'.mulVec (X.u (1 - g) q) = s q • X.u (1 - g) q) → ∀ a ∈ Cv X V g, ((fun i => ∑ j, M i j • a.1 j, fun q => s q • a.2 q) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g := by sorry
