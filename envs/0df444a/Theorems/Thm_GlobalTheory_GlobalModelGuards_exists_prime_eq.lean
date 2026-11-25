-- Prove2me | Theorems.Thm_GlobalTheory_GlobalModelGuards_exists_prime_eq
-- name    : GlobalTheory.GlobalModelGuards.exists_prime_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:53.455803+00:00
-- url     : https://prove2.me/theorems/f87f2b59-5769-58f0-a49d-40529bd33f01
-- title:
--   Global Model Guards: exists prime eq
-- statement:
--   The Global Model Guards construction uses the exists prime eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/ExistsGoodLevel.lean#L180-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/ExistsGoodLevel.lean#L180-L215

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_ExistsGoodLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GlobalModelGuards
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem GlobalTheory.GlobalModelGuards.exists_prime_eq {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (p : ℕ) (hp : p.Prime)
    (hW : (p : ℂ) ∈ W.nonunits) [NumberField c.F] :
    ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F), (p : 𝓞 c.F) ∈ v.asIdeal ∧
      v.valuationSubringAtPrime c.F = c.V W := by sorry
