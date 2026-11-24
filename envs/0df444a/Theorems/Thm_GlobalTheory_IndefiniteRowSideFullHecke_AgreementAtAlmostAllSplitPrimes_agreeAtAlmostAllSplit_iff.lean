-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_AgreementAtAlmostAllSplitPrimes_agreeAtAlmostAllSplit_iff
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes.agreeAtAlmostAllSplit_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:47:34.314161+00:00
-- url     : https://prove2.me/theorems/453f344c-d0e3-4909-82f6-171e2007d8e5
-- title:
--   Agreement At Almost All Split Primes: agree At Almost All Split iff
-- statement:
--   The Agreement At Almost All Split Primes construction uses the agree At Almost All Split iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ThetaLiftGeometry/AgreementAtAlmostAllSplitPrimes.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ThetaLiftGeometry/AgreementAtAlmostAllSplitPrimes.lean#L17-L21

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_AgreementAtAlmostAllSplitPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes

theorem GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes.agreeAtAlmostAllSplit_iff {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    (A : NAut N) (χ χ' : A.CG 1) :
    AgreeAtAlmostAllSplit A χ χ' ↔
      ∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locG χ w = A.locG χ' w := by sorry
