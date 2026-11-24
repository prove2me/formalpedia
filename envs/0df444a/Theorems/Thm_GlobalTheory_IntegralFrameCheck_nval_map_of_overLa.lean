-- Prove2me | Theorems.Thm_GlobalTheory_IntegralFrameCheck_nval_map_of_overLa
-- name    : GlobalTheory.IntegralFrameCheck.nval_map_of_overLa
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:19:56.803861+00:00
-- url     : https://prove2.me/theorems/fa255903-de6a-44ab-9cc4-1544f9fb168f
-- title:
--   Integral Frame Check: nval map of over La
-- statement:
--   The Integral Frame Check construction uses the nval map of over La property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/VVAlgebraMapNonneg.lean#L94-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/VVAlgebraMapNonneg.lean#L94-L113

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_VVAlgebraMapNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IntegralFrameCheck
open Formalism.L2.Pj NumberField IsDedekindDomain
open scoped WithZero

theorem GlobalTheory.IntegralFrameCheck.nval_map_of_overLa {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)}
    {T T' : CDVR} {io : K →+* T.Fr} {io' : K →+* T'.Fr} {e e' : ℕ}
    (ho : OverLa la T.V io e) (ho' : OverLa la T'.V io' e') (i : T.Fr →+* T'.Fr)
    (hc : ∀ a, i (io a) = io' a)
    (hi : ∀ a : T.V, i (algebraMap T.V T.Fr a) ∈ Set.range (algebraMap T'.V T'.Fr)) :
    ∃ r : ℕ, 0 < r ∧ e' = r * e ∧ (∀ x, vV T'.V (i x) = (r : ℤ) * vV T.V x) ∧
      ∀ x, nval T'.V e' (i x) = nval T.V e x := by sorry
