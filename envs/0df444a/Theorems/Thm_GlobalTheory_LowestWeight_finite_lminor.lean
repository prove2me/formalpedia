-- Prove2me | Theorems.Thm_GlobalTheory_LowestWeight_finite_lminor
-- name    : GlobalTheory.LowestWeight.finite_lminor
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:19:46.107866+00:00
-- url     : https://prove2.me/theorems/b84c349c-bbba-4330-8627-22bdb54c2751
-- title:
--   Lowest Weight: finite lminor
-- statement:
--   The Lowest Weight construction uses the finite lminor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L107-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L107-L120

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LowestWeightFunctionMulEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix Filter Topology
open scoped ComplexConjugate ComplexOrder
open GlobalTheory.LowestWeight
variable {r : ℕ}

theorem GlobalTheory.LowestWeight.finite_lminor (Y : Matrix (Fin r) (Fin r) ℂ) (i : Fin (r + 1)) :
    {s : ℂ | lminor (Y + s • (1 : Matrix (Fin r) (Fin r) ℂ)) i = 0}.Finite := by sorry
