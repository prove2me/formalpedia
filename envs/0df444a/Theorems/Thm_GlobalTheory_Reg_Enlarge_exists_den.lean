-- Prove2me | Theorems.Thm_GlobalTheory_Reg_Enlarge_exists_den
-- name    : GlobalTheory.Reg.Enlarge.exists_den
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:13:58.374695+00:00
-- url     : https://prove2.me/theorems/150364c3-37fd-4cb2-9a3b-2eca9615eda0
-- title:
--   Enlarge: exists den
-- statement:
--   The Enlarge construction uses the exists den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralFlagChartEnlargeContainingValue.lean#L16-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralFlagChartEnlargeContainingValue.lean#L16-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralFlagChartEnlargeContainingValue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Enlarge
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain Polynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem GlobalTheory.Reg.Enlarge.exists_den {K Ω O : Type} [Field K] [Field Ω] [Algebra K Ω] [CommRing O] [IsDomain O] [Algebra O K]
    [IsFractionRing O K] (gs : Set Ω) {g : Ω} (hg : g ∈ Algebra.adjoin K gs) :
    ∃ d : O, d ≠ 0 ∧ algebraMap K Ω (algebraMap O K d) * g ∈
      Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gs) := by sorry
