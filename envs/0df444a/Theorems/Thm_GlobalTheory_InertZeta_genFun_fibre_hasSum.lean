-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_genFun_fibre_hasSum
-- name    : GlobalTheory.InertZeta.genFun_fibre_hasSum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:18:33.240881+00:00
-- url     : https://prove2.me/theorems/b3c45eca-8686-4183-8407-eb08244e17de
-- title:
--   Inert Zeta: gen Fun fibre has Sum
-- statement:
--   The Inert Zeta construction uses the gen Fun fibre has Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LengthCountGeneratingSeriesFormula.lean#L61-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LengthCountGeneratingSeriesFormula.lean#L61-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LengthCountGeneratingSeriesFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
noncomputable section
open GlobalTheory GlobalTheory.InertZeta

theorem GlobalTheory.InertZeta.genFun_fibre_hasSum {ι 𝕜 : Type} [NormedField 𝕜] (f : ι → ℕ) (l j : ℕ) (x : 𝕜)
    (hfin : Set.Finite {i | f i - l = j}) (hl : ∀ i, l ≤ f i) :
    HasSum (fun y : {i // f i - l = j} => x ^ f y.1) ((Set.ncard {i | f i - l = j} : 𝕜) * x ^ (l + j)) := by sorry
