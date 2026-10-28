-- Prove2me | Theorems.Thm_GuhaEPnI_MinOutput_gInv_properties
-- name    : GuhaEPnI.MinOutput.gInv_properties
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:15.2648+00:00
-- url     : https://prove2.me/theorems/e8676527-252b-4dd0-9964-777949a4a6b7
-- title:
--   §II.B, p. 2 — inverse thermal entropy is nonnegative, increasing, and convex
-- statement:
--   The thermal entropy function $g$ has an inverse on the nonnegative reals. For every $t,s\ge 0$,
--
--   $$g^{-1}(g(t))=t,\qquad g(g^{-1}(s))=s.$$
--
--   The inverse is nonnegative, increasing, and convex on $[0,\infty)$.
--
--   This gives the entropy photon-number $g^{-1}(S/n)$ used in Eq. (11) and throughout the EPnI.
--
--   **Formalization Note** The published definition represents $g^{-1}(s)$ as the infimum of nonnegative $t$ with $s\le g(t)$; the theorem confirms that this is the genuine inverse on the stated domain.
-- source:
--   Guha, Erkmen & Shapiro, The Entropy Photon-Number Inequality and its Consequences, arXiv:0710.5666v2, p. 2, §II.B, paragraph after Eq. (10)

import Mathlib
import Definitions.Def_EntropyPhotonNumber

namespace GuhaEPnI.MinOutput
open OAI.EntropyPhotonNumber

theorem gInv_properties :
    (∀ t : ℝ, 0 ≤ t → gInv (g t) = t) ∧
    (∀ s : ℝ, 0 ≤ s → g (gInv s) = s) ∧
    (∀ s : ℝ, 0 ≤ s → 0 ≤ gInv s) ∧
    MonotoneOn gInv (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) gInv := by sorry

end GuhaEPnI.MinOutput
