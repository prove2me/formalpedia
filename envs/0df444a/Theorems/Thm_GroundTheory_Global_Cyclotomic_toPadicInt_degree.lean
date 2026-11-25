-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_toPadicInt_degree
-- name    : GroundTheory.Global.Cyclotomic.toPadicInt_degree
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:36:17.810265+00:00
-- url     : https://prove2.me/theorems/dcadd5a5-2255-4b7b-a112-c1272b57c35e
-- title:
--   Cyclotomic: to Padic Int degree
-- statement:
--   The Cyclotomic construction uses the to Padic Int degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Degree.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Degree.lean#L102-L105

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_PadicUnitsLog
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
open scoped GroundTheory.LocalField.Abstract ComplexConjugate
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ

theorem GroundTheory.Global.Cyclotomic.toPadicInt_degree (q : Nat.Primes) (σ : Gal(ℚ̄/ℚ)) :
    toPadicInt q (Multiplicative.toAdd (degree σ)) = Multiplicative.toAdd (degreeComponent q σ) := by sorry
