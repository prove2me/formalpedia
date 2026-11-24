-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_coeff_single_law_add
-- name    : GlobalTheory.FormalCalc.coeff_single_law_add
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:34:29.890946+00:00
-- url     : https://prove2.me/theorems/208dcea0-6030-44e8-9b66-5f2e30ce912e
-- title:
--   Formal Calc: coeff single law add
-- statement:
--   The Formal Calc construction uses the coeff single law add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/CoeffSingleLawAdd.lean#L93-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/CoeffSingleLawAdd.lean#L93-L100

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalCalc
variable {R : Type} [CommRing R] {d : ℕ}

theorem GlobalTheory.FormalCalc.coeff_single_law_add {n : ℕ} (G : FGLaw R d) (p q : Pt R n d)
    (hp : ∀ i, constantCoeff (p i) = 0) (hq : ∀ i, constantCoeff (q i) = 0) (i : Fin d)
    (j : Fin n × Fin d) :
    coeff (Finsupp.single j 1) (G.add p q i) =
      coeff (Finsupp.single j 1) (p i) + coeff (Finsupp.single j 1) (q i) := by sorry
