-- Prove2me | Theorems.Thm_GlobalTheory_Up_Definite_gram_one
-- name    : GlobalTheory.Up.Definite.gram_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:24.408729+00:00
-- url     : https://prove2.me/theorems/0986c3b0-0c9c-4e28-b12e-ea1296046f2a
-- title:
--   Definite: gram one
-- statement:
--   The Definite construction uses the gram one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/UpperBounds/SingleMemIntVec.lean#L177-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/UpperBounds/SingleMemIntVec.lean#L177-L180

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_IsStrictDom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SingleMemIntVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate ComplexOrder Matrix
open GlobalTheory GlobalTheory.Up GlobalTheory.Up.Definite
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.Up.Definite.gram_one (τ : E →+* ℂ) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ (1 : Matrix (Fin r) (Fin r) E) x = (x.map conj)ᴴ * x.map conj := by sorry
