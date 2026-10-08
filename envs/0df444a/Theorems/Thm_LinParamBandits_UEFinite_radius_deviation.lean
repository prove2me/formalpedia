-- Prove2me | Theorems.Thm_LinParamBandits_UEFinite_radius_deviation
-- name    : LinParamBandits.UEFinite.radius_deviation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:03:27.532836+00:00
-- url     : https://prove2.me/theorems/4266991e-f287-4a4f-8c3e-bbfcadeb05ee
-- title:
--   Lemma B.6 — large deviation inequalities for the uncertainty radius, ≤ 1/t²
-- statement:
--   Consider the linearly parameterized bandit of Rusmevichientong and Tsitsiklis under Assumption 1, with a compact nonempty set of arms $\mathcal U_r \subset \mathbb R^r$ ($r \ge 2$), finite or infinite, run by the Uncertainty Ellipsoid policy, with $\alpha = 4\sigma_0\kappa_0^2$ and uncertainty radius $R^u_t = \alpha\sqrt{\log t}\sqrt{\min\{r\log t, |\mathcal U_r|\}}\,\|u\|_{C_t}$. For every $t \ge r$ and $z \in \mathbb R^r$:
--
--   1. for every arm $u \in \mathcal U_r$,
--   $$\Pr\Big\{u'(\widehat Z_t - z) > R^u_t \;\Big|\; Z = z\Big\} \le \frac{1}{t^2};$$
--   2. for every $x \in \mathbb R^r$,
--   $$\Pr\Big\{(U_{t+1} - x)'(\widehat Z_t - z) > \alpha\sqrt{\log t}\sqrt{\min\{r\log t, |\mathcal U_r|\}}\,\|U_{t+1} - x\|_{C_t} \;\Big|\; Z = z\Big\} \le \frac{1}{t^2}.$$
--
--   The radius is calibrated exactly so that the probability of overestimating an arm's reward by more than $R^u_t$ is summable in $t$; this is what bounds the number of pulls of a suboptimal arm.
--
--   **Formalization Note** $|\mathcal U_r|$ is `Set.ncard`; for an infinite arm set $\min\{r\log t, |\mathcal U_r|\}$ is read as $r\log t$ (the `width` split), as on the page.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Lemma B.6, p. 34

import Mathlib
import Definitions.Def_LinParamBandits_UEFinite_Model
import Definitions.Def_LinParamBandits_UEFinite_UEPolicy

namespace LinParamBandits.UEFinite

open MeasureTheory ProbabilityTheory

theorem radius_deviation
    (σ₀ ū lam₀ : ℝ) (hσ₀ : 0 < σ₀) (hū : 0 < ū) (hlam₀ : 0 < lam₀)
    (r : ℕ) (hr : 2 ≤ r) (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰cpt : IsCompact 𝒰) (h𝒰ne : 𝒰.Nonempty)
    (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) (hν : IsMarkovKernel ν) (hnoise : NoiseAssumption 𝒰 ν σ₀)
    (b : Fin r → LinParamBandits.LowerBound.Vec r) (harms : ArmAssumption 𝒰 b ū lam₀)
    (ψ : LinParamBandits.UEGeneral.Policy r) (hψ : IsUE 𝒰 b σ₀ ū lam₀ ψ)
    (t : ℕ) (ht : r ≤ t) (z : LinParamBandits.LowerBound.Vec r) :
    (∀ u ∈ 𝒰, LinParamBandits.UEGeneral.histMeasure ν z ψ t {h | inner ℝ u (LinParamBandits.UEGeneral.Zhat h - z) > radius σ₀ ū lam₀ 𝒰 h u} ≤
        ENNReal.ofReal (1 / (t : ℝ) ^ 2)) ∧
    (∀ x : LinParamBandits.LowerBound.Vec r, LinParamBandits.UEGeneral.histMeasure ν z ψ t {h | inner ℝ (ψ.act t h - x) (LinParamBandits.UEGeneral.Zhat h - z) >
        alpha σ₀ ū lam₀ * Real.sqrt (Real.log t) * Real.sqrt (LinParamBandits.UEGeneral.width 𝒰 t) *
          normC h (ψ.act t h - x)} ≤
        ENNReal.ofReal (1 / (t : ℝ) ^ 2)) := by sorry

end LinParamBandits.UEFinite
