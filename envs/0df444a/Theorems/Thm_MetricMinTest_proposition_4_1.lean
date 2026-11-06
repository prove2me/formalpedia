-- Prove2me | Theorems.Thm_MetricMinTest_proposition_4_1
-- name    : MetricMinTest.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:07:45.521629+00:00
-- url     : https://prove2.me/theorems/3e8d7f15-666c-47fe-90af-5326bf1b4953
-- title:
--   Proposition 4.1, p.8 — workloads of a hierarchy: $H=k/\kappa$, $F=k\min_t 1/(b^tg_t^2)$
-- statement:
--   Fix integers $b\ge2$, $m\ge1$, let $V=\{0,\dots,b-1\}^m$, $k=b^m$, and let $\gamma=g_0\ge g_1\ge\dots\ge g_m\ge0$ be a gap profile with $\gamma>0$, defining the hierarchical metric $d_g(x,y)=\gamma-g_{\mathrm{lev}(x,y)}$. With $v_0=1$, $v_t=b^t-b^{t-1}$ and $\kappa=\sum_{t=0}^mv_tg_t^2$,
--   $$H_{d_g}(\gamma)=\frac k\kappa,\qquad F_{d_g}(\gamma)=k\min_{0\le t\le m:\ g_t>0}\frac1{b^tg_t^2}.$$
--
--   Both workloads of a hierarchy are thus explicit functions of the gap profile; the critical metric of Theorem A is the case $b=4$, $g_t=\gamma2^{-t}$.
--
--   **Formalization Note** The minimum over levels is an infimum over the finite nonempty set of levels $t\le m$ with $g_t>0$ (nonempty since $g_0=\gamma>0$).
--
--   Differences from the source:
--   - generalization: standing margin $\gamma\in(0,1/4]$ → any $\gamma>0$; reason: the proposition does not use $\gamma\le1/4$; it specializes to the standing range
--   - encoding: $\min_{0\le t\le m: g_t>0}$ → real infimum over the finite nonempty subtype of such levels; reason: Lean convention; same value
--   - encoding: the minima $H_d(\gamma)$ of (1.1) and $F_d(\gamma)$ of (2.1) over indexed balls $B_{j\ell}$ → real infima of the feasible values, with indexed balls encoded by the pairs $(j,i)$ with $d(j,i)<\gamma$; reason: the minima are attained (pp.6–7) and a repeated distance only duplicates a ball at equal cost, so the values are the same
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Proposition 4.1, p.8

import Mathlib
import Definitions.Def_MetricMinTest_IsGapProfile
import Definitions.Def_MetricMinTest_gapMetric
import Definitions.Def_MetricMinTest_kappa
import Definitions.Def_MetricMinTest_infoWorkload
import Definitions.Def_MetricMinTest_certWorkload

namespace MetricMinTest

/-- **Proposition 4.1 (Workloads of a hierarchy).** Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Proposition 4.1, p.8: "For
every gap profile, H_{d_g}(γ) = k/κ, F_{d_g}(γ) = k min_{0≤t≤m: g_t>0} 1/(b^t g_t²)."

**Formalization Note.** Standing setting of §4.1: `b ≥ 2`, `m ≥ 1`, `V = Fin m → Fin b`,
`k = b^m`. The margin is only required positive (the standing `γ ≤ 1/4` is not used). The minimum
over levels is the real `⨅` over the finite nonempty type of levels `t ≤ m` with `g_t > 0`
(nonempty: `g₀ = γ > 0`). -/
theorem proposition_4_1 (b m : ℕ) (hb : 2 ≤ b) (hm : 1 ≤ m) (γ : ℝ) (hγ : 0 < γ) (g : ℕ → ℝ)
    (hg : IsGapProfile m γ g) :
    infoWorkload (gapMetric b m g) γ = (b : ℝ) ^ m / kappa b m g ∧
    certWorkload (gapMetric b m g) γ =
      (b : ℝ) ^ m * ⨅ t : {t : ℕ // t ≤ m ∧ 0 < g t}, 1 / ((b : ℝ) ^ (t : ℕ) * g t ^ 2) := by sorry

end MetricMinTest
