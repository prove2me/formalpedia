-- Prove2me | Theorems.Thm_Kawahira_symmetric_indifferent_zero_simple
-- name    : Kawahira.symmetric_indifferent_zero_simple
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T22:46:02.003279+00:00
-- url     : https://prove2.me/theorems/e0e3babc-394f-464a-a2b2-e2867864bd12
-- title:
--   Symmetric indifferent zeros lie simply on the critical line
-- statement:
--   Let an entire function have finite vanishing order everywhere and be symmetric under reflection $s\mapsto1-s$. If every nonzero zero is an indifferent fixed point of its associated map $\nu_g$, then each zero in the open critical strip lies on the critical line and is simple.
-- source:
--   Abstracted symmetric-pair multiplicity argument from T. Kawahira, The Riemann Hypothesis and Holomorphic Index in Complex Dynamics (2016), Theorem 11.

import Definitions.Def_Kawahira_zeta
import Theorems.Thm_Kawahira_nu_indifferent_zero_order_re

open Complex Topology

namespace Kawahira

theorem symmetric_indifferent_zero_simple (g : ℂ → ℂ)
    (hg : ∀ a : ℂ, AnalyticAt ℂ g a)
    (hfinite : ∀ a : ℂ, analyticOrderAt g a ≠ ⊤)
    (hsymm : ∀ z : ℂ, g (1 - z) = g z)
    (hind : ∀ a : ℂ, a ≠ 0 → g a = 0 → IsIndifferentFixedPoint (nu g) a)
    (s : ℂ) (hszero : g s = 0) (hstrip : 0 < s.re ∧ s.re < 1) :
    s.re = 1 / 2 ∧ deriv g s ≠ 0 := by sorry
