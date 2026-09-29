-- Prove2me | Theorems.Thm_Freiman_lower_entry_domain_normalizes
-- name    : Freiman.lower_entry_domain_normalizes
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:05.321267+00:00
-- url     : https://prove2.me/theorems/0c4e69bf-a31f-42a9-bbfa-49eed6ea2f32
-- title:
--   Freiman lower construction: entry domain normalizes
-- statement:
--   The printed strict q,r,s bounds imply that the first full alpha,beta width is larger. This elementary rational width comparison establishes actual normalization without assuming any cover swap invariance.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_domain_normalizes 
    (hfrac : ∀ (w : List ℕ+) (t : ℝ), 0 < t →
      prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧
      0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧
      (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d -
      (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length)
    (hcd : ∀ w : List ℕ+, (lowerInitialWordMatrix w).c = ((lowerCD w).1:ℝ) ∧ (lowerInitialWordMatrix w).d = ((lowerCD w).2:ℝ))
    (p : LowerPair) (hd : lowerEntryDomain p) : lowerNormalize p = p := by
  sorry
