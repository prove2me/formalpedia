-- Prove2me | Theorems.Thm_Kawahira_nu_indifferent_zero_order_re
-- name    : Kawahira.nu_indifferent_zero_order_re
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T22:29:04.662477+00:00
-- url     : https://prove2.me/theorems/d75ac480-4610-435c-bc91-fb77983f09ae
-- title:
--   Real-part constraint for an indifferent ν fixed point
-- statement:
--   Let $a\ne0$ be a zero of positive finite order $m$ of an analytic function $g$. If $a$ is an indifferent fixed point of the associated map $\nu_g$, then $m\operatorname{Re}(a)=1/2$. This isolates the reusable local multiplier calculation from applications to paired zeta zeros.
-- source:
--   T. Kawahira, The Riemann Hypothesis and Holomorphic Index in Complex Dynamics, Experimental Mathematics (2016), https://doi.org/10.1080/10586458.2016.1217443, local multiplier calculation in Propositions 5 and 9.

import Definitions.Def_Kawahira_zeta
import Theorems.Thm_Kawahira_nu_at_zero_of_order
import Theorems.Thm_Kawahira_norm_one_sub_inv

open Complex Topology

namespace Kawahira

theorem nu_indifferent_zero_order_re (g : ℂ → ℂ) (a : ℂ) (m : ℕ)
    (ha : a ≠ 0) (hm : 1 ≤ m) (hg : AnalyticAt ℂ g a)
    (horder : analyticOrderAt g a = (m : ℕ∞))
    (hind : IsIndifferentFixedPoint (nu g) a) :
    (m : ℝ) * a.re = 1 / 2 := by sorry
