-- Prove2me | Theorems.Thm_GlobalTheory_GaussCusp_dmin_one
-- name    : GlobalTheory.GaussCusp.dmin_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:29.453651+00:00
-- url     : https://prove2.me/theorems/d40db17b-1c2b-4489-8f3a-77c63995a209
-- title:
--   Gauss Cusp: dmin one
-- statement:
--   The Gauss Cusp construction uses the dmin one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FirstRaisingMemEquivariant.lean#L337-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FirstRaisingMemEquivariant.lean#L337-L342

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementHypsConsistent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FirstRaisingMemEquivariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries (E4)
open GlobalTheory
open GlobalTheory.GaussCusp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {ζ : E}

theorem GlobalTheory.GaussCusp.dmin_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ 1) (τ : Ψ) :
    dmin (1 : Matrix (Fin 1) (Fin 1) E) x τ (Fin.succ 0) = ((‖x τ 0 0‖ ^ 2 : ℝ) : ℂ) := by sorry
