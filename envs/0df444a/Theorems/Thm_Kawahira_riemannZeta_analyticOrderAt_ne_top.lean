-- Prove2me | Theorems.Thm_Kawahira_riemannZeta_analyticOrderAt_ne_top
-- name    : Kawahira.riemannZeta_analyticOrderAt_ne_top
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T22:05:37.253191+00:00
-- url     : https://prove2.me/theorems/a55e70b8-8ff4-413e-b394-da34c4c7b69e
-- title:
--   Every regular point of the Riemann zeta function has finite analytic order
-- statement:
--   At every complex point other than its pole at $1$, the Riemann zeta function has finite analytic order. Equivalently, zeta cannot vanish identically on a neighborhood of any regular point. This provides the finite multiplicity needed for local zero dynamics.
-- source:
--   Identity theorem for holomorphic functions applied to the Riemann zeta function on $\mathbb{C}\setminus\{1\}$; compare T. Kawahira (2016), local multiplicity assumptions in Propositions 5 and 8, https://doi.org/10.1080/10586458.2016.1217443.

import Definitions.Def_Kawahira_zeta

open Complex Topology Set

namespace Kawahira

theorem riemannZeta_analyticOrderAt_ne_top (a : ℂ) (ha : a ≠ 1) :
    analyticOrderAt riemannZeta a ≠ ⊤ := by sorry
