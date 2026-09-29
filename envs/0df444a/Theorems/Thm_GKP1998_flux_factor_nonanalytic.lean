-- Prove2me | Theorems.Thm_GKP1998_flux_factor_nonanalytic
-- name    : GKP1998.flux_factor_nonanalytic
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:53:22.48973+00:00
-- url     : https://prove2.me/theorems/fa90c5a5-8ed7-40ee-ad30-2b788c463cbe
-- title:
--   Eqs. (43)–(44): leading non-analytic term of the flux factor for non-integer $\nu$
-- statement:
--   For every real $\nu>0$ with $\nu\notin\mathbb Z$ and every $R>0$, there is a function $A$, real-analytic at $0$, such that as $k\to0^+$
--   $$\mathcal F_\nu(k)=A(k^2)-2\nu\,\frac{\Gamma(1-\nu)}{\Gamma(1+\nu)}\Big(\frac{kR}{2}\Big)^{2\nu}R^{-4}+o\big(k^{2\nu}\big).$$
--   Multiplied by $N^2/(16\pi^2)$ this is Eq. (44), since $\nu\Gamma(1-\nu)/\Gamma(1+\nu)=\Gamma(1-\nu)/\Gamma(\nu)$.
-- source:
--   S.S. Gubser, I.R. Klebanov, A.M. Polyakov, Gauge theory correlators from non-critical string theory, Phys. Lett. B 428 (1998) 105-114, arXiv:hep-th/9802109, p. 112, Eqs. (43)-(44)

import Definitions.Def_GKP1998_Defs

open Filter Topology Asymptotics

namespace GKP1998
/-- Eqs. (43)–(44), flux-factor form: for non-integer `ν > 0` the flux factor is an analytic
function of `k²` plus the leading non-analytic term
`−2ν Γ(1−ν)/Γ(1+ν) · (kR/2)^{2ν} · R⁻⁴`, up to `o(k^{2ν})` as `k → 0⁺`. -/
theorem flux_factor_nonanalytic (ν R : ℝ) (hν : 0 < ν) (hνZ : ∀ n : ℤ, ν ≠ n) (hR : 0 < R) :
    ∃ A : ℝ → ℝ, AnalyticAt ℝ A 0 ∧
      (fun k : ℝ => fluxFactor ν k R - A (k ^ 2)
          - (-2 * ν * Real.Gamma (1 - ν) / Real.Gamma (1 + ν) * (k * R / 2) ^ (2 * ν) / R ^ 4))
        =o[𝓝[>] (0 : ℝ)] (fun k : ℝ => k ^ (2 * ν)) := by sorry
end GKP1998
