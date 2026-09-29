-- Prove2me | Theorems.Thm_Kawahira_xi_analyticOrderAt_ne_top
-- name    : Kawahira.xi_analyticOrderAt_ne_top
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T22:43:55.666564+00:00
-- url     : https://prove2.me/theorems/d7621046-1db8-49e4-849b-f518e02b360e
-- title:
--   The Riemann xi function has finite analytic order at every point
-- statement:
--   The normalized Riemann xi function has finite vanishing order at every complex point. This follows because xi is entire and is not identically zero.
-- source:
--   Identity theorem for entire functions, applied to the normalized Riemann xi function.

import Definitions.Def_Kawahira_zeta

open Complex Topology Set

namespace Kawahira

theorem xi_analyticOrderAt_ne_top (a : ℂ) : analyticOrderAt xi a ≠ ⊤ := by sorry
