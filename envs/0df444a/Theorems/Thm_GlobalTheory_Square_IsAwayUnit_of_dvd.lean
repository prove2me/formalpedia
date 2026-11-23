-- Prove2me | Theorems.Thm_GlobalTheory_Square_IsAwayUnit_of_dvd
-- name    : GlobalTheory.Square.IsAwayUnit.of_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:10.925806+00:00
-- url     : https://prove2.me/theorems/5ccf6a29-d910-4909-b211-8d40c9daaccf
-- title:
--   Is Away Unit: of dvd
-- statement:
--   The Is Away Unit construction uses the of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L132-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L132-L133

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
noncomputable section
open GlobalTheory GlobalTheory.Square
variable {K : Type} [Field K] [NumberField K] [StarRing K]
attribute [instance] Co.finX
attribute [instance] Sq.finκ
omit [NumberField K] [StarRing K]

theorem GlobalTheory.Square.IsAwayUnit.of_dvd {m k : ℕ} {a : 𝓞 K} (h : a ∣ (m : 𝓞 K) ^ k) : IsAwayUnit m (a : K) := by sorry
