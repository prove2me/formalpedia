-- Prove2me | Theorems.Thm_Freiman_lower_initial_gluing
-- name    : Freiman.lower_initial_gluing
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:06.649864+00:00
-- url     : https://prove2.me/theorems/c26832cd-bd1e-4018-a244-2ee3e432185a
-- title:
--   Freiman lower construction: initial gluing
-- statement:
--   Topological gluing of the parity chains, their common run limits, n contacts and fixed-root union. The hypotheses are the explicit source word comparisons; no closedness of a spectrum is assumed.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, proof of prop:lc-H-contacts

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_initial_gluing (hseams : lowerInitialSeams) (hlimits : lowerInitialLimits)
    (hfixed : IsPreconnected {t : ℝ | ∃ p ∈ lowerFixedRoots, t ∈ lowerCover p})
    (hoverlap : (lowerCover ([3,2,1,1,3],[4,3,2,2]) ∩ lowerFamilyH .A 0 1 0).Nonempty) :
    IsPreconnected lowerInitialSet := by
  sorry
