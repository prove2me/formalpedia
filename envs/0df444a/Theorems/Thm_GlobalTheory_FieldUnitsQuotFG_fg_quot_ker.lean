-- Prove2me | Theorems.Thm_GlobalTheory_FieldUnitsQuotFG_fg_quot_ker
-- name    : GlobalTheory.FieldUnitsQuotFG.fg_quot_ker
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:24:47.154322+00:00
-- url     : https://prove2.me/theorems/ad162b96-e241-46b5-a0f0-e2a3c904da31
-- title:
--   Field Units Quot FG: fg quot ker
-- statement:
--   The Field Units Quot FG construction uses the fg quot ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FgUnitsQuotIntegralUnitsFiniteFieldExt.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FgUnitsQuotIntegralUnitsFiniteFieldExt.lean#L9-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsFiniteFieldExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.FieldUnitsQuotFG

theorem GlobalTheory.FieldUnitsQuotFG.fg_quot_ker {G S : Type} [CommGroup G] [Finite S] (φ : G →* (S → Multiplicative ℤ)) :
    Group.FG (G ⧸ φ.ker) := by sorry
