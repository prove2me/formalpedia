-- Prove2me | Theorems.Thm_GlobalTheory_DenseCompl_asIdeal_eq_span
-- name    : GlobalTheory.DenseCompl.asIdeal_eq_span
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:11:19.532603+00:00
-- url     : https://prove2.me/theorems/649de8e2-0c7d-4993-a846-88141726aeb5
-- title:
--   Dense Compl: as Ideal eq span
-- statement:
--   The Dense Compl construction uses the as Ideal eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EqZeroOfForallLeExp.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EqZeroOfForallLeExp.lean#L20-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousOfValuationEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EqZeroOfForallLeExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open WithZero
open GlobalTheory GlobalTheory.DenseCompl
variable {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [IsFractionRing W Qq]

theorem GlobalTheory.DenseCompl.asIdeal_eq_span {π : W} (hπ : Irreducible π) (v : HeightOneSpectrum W) :
    v.asIdeal = Ideal.span {π} := by sorry
