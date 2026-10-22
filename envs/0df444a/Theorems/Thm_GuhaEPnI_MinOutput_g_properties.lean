-- Prove2me | Theorems.Thm_GuhaEPnI_MinOutput_g_properties
-- name    : GuhaEPnI.MinOutput.g_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:16.642821+00:00
-- url     : https://prove2.me/theorems/fbc8f5f2-ba88-44e2-8c0f-fc02467c6aba
-- title:
--   §II.B, p. 2 — nonnegativity, increase, and concavity of thermal entropy
-- statement:
--   Let $g(t)=(t+1)\log(t+1)-t\log t$ denote the entropy of a thermal state with mean photon number $t$. On $[0,\infty)$, $g$ is nonnegative, increasing, and concave:
--
--   $$g(t)\ge0\quad(t\ge0),\qquad t\le u\Longrightarrow g(t)\le g(u).$$
--
--   These scalar properties identify thermal entropy as an increasing measure of mean photon number and support its inversion in the EPnI.
-- source:
--   Guha, Erkmen & Shapiro, The Entropy Photon-Number Inequality and its Consequences, arXiv:0710.5666v2, p. 2, §II.B, paragraph after Eq. (10)

import Mathlib
import Definitions.Def_EntropyPhotonNumber

namespace GuhaEPnI.MinOutput
open OAI.EntropyPhotonNumber

theorem g_properties :
    (∀ t : ℝ, 0 ≤ t → 0 ≤ g t) ∧
    MonotoneOn g (Set.Ici 0) ∧
    ConcaveOn ℝ (Set.Ici 0) g := by sorry

end GuhaEPnI.MinOutput
