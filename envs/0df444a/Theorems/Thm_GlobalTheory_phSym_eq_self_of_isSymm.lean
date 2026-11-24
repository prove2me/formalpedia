-- Prove2me | Theorems.Thm_GlobalTheory_phSym_eq_self_of_isSymm
-- name    : GlobalTheory.phSym_eq_self_of_isSymm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:00.549804+00:00
-- url     : https://prove2.me/theorems/aedef81b-2789-4aec-9661-a1efd780db70
-- title:
--   Global Theory: ph Sym eq self of is Symm
-- statement:
--   The Global Theory construction uses the ph Sym eq self of is Symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine.lean#L33-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open GlobalTheory
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key
variable {g : ℕ}
open Complex Matrix
variable {g : ℕ}

theorem GlobalTheory.phSym_eq_self_of_isSymm {x : Matrix (Fin g) (Fin g) ℂ} (hx : x.IsSymm) :
    _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym x = x := by sorry
