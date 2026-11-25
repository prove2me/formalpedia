-- Prove2me | Theorems.Thm_GlobalTheory_Pat_PolGp_finite_cocycles
-- name    : GlobalTheory.Pat.PolGp.finite_cocycles
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:19.700938+00:00
-- url     : https://prove2.me/theorems/571a201f-9347-5679-9e8f-7b362481f668
-- title:
--   Pol Gp: finite cocycles
-- statement:
--   The Pol Gp construction uses the finite cocycles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean#L315-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean#L315-L324

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Polynomial IsLocalRing
noncomputable section
open IsLocalRing
open GlobalTheory GlobalTheory.Pat
attribute [instance] PG.grp PG.top PG.tgrp PG.cpt PG.t2 PG.td
attribute [instance] Frame.hl Frame.iO Frame.iOd Frame.iOv Frame.iVl Frame.iSt

theorem GlobalTheory.Pat.PolGp.finite_cocycles {Φ : Frame} (G : PolGp Φ) (i i' : Fin Φ.n) :
    {b : G.Γ → Φ.k | IsLocallyConstant b ∧ ∀ g h, b (g * h) =
      ((G.chi i g : Φ.kˣ) : Φ.k) * b h + b g * ((G.chi i' h : Φ.kˣ) : Φ.k)}.Finite := by sorry
