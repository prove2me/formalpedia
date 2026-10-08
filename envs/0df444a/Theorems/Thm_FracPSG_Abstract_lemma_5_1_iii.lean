-- Prove2me | Theorems.Thm_FracPSG_Abstract_lemma_5_1_iii
-- name    : FracPSG.Abstract.lemma_5_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:10:18.349971+00:00
-- url     : https://prove2.me/theorems/0561aec8-442d-4f2d-a241-5b98a234d323
-- title:
--   Lemma 5.1(iii) — subgradient bound and stationarity on Ω₀
-- statement:
--   In the setting of §5, suppose (H1), (H2) and (H3) hold, and that $\underline\delta:=\inf_{n\in\mathbb N,i\in I}\alpha_{n-i}\beta_n^2>0$; concretely, let $d>0$ satisfy $d\le\alpha_{n-i}\beta_n^2$ for all $n\in\mathbb N$, $i\in I$ with $n-i\ge0$. Then for every $n\ge\max\{0,\bar\imath\}$,
--   $$\operatorname{dist}\big(0,\partial_L h(z_n)\big)\le\sqrt{\frac{h(z_{n-\bar\imath})-h(z_{n+1-\underline\imath})}{d}}+\frac{\varepsilon_n}{\beta_n}.$$
--   If in addition $\varepsilon_n/\beta_n\to0$, then $0\in\partial_L h(\bar z)$ for every $\bar z\in\Omega_0$.
--
--   The bound converts the multi-step relative error condition into a single-step subgradient estimate in terms of value decrease, and its limit gives stationarity of the cluster points in $\Omega_0$.
--
--   **Formalization Note** The distance bound is stated as the existence of $v\in\partial_L h(z_n)$ with $\|v\|$ at most the right-hand side (equivalent, since $\partial_L h(z_n)$ is closed and $\operatorname{dist}(0,\emptyset)=+\infty$). The indices $n-\bar\imath\ge0$ and $n+1-\underline\imath\ge1$ are natural numbers for $n\ge\bar\imath$ and are converted with `Int.toNat`. $\underline\imath$ and $\bar\imath$ are `ilo` and `ihi`.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 14, Lemma 5.1(iii)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_FracPSG_Abstract_Basic

open Filter Topology

namespace FracPSG.Abstract

open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

/-- Lemma 5.1(iii) (Boţ–Dao–Li, arXiv:2003.04124v2, p. 14): under (H1), (H2), (H3) and
`δ̲ = inf_{n, i ∈ I} α_{n-i}βₙ² > 0` (here: any `d > 0` bounding these products from below), for every
`n ≥ max{0, ı̄}`, `dist(0, ∂_L h(zₙ)) ≤ √((h(z_{n-ı̄}) - h(z_{n+1-ı̲}))/d) + εₙ/βₙ`; and if moreover
`εₙ/βₙ → 0`, then `0 ∈ ∂_L h(z̄)` for every `z̄ ∈ Ω₀`. -/
theorem lemma_5_1_iii {P : ℕ} {h : EuclideanSpace ℝ (Fin P) → EReal}
    {z : ℕ → EuclideanSpace ℝ (Fin P)} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ} {ilo ihi : ℤ}
    {lam : ℤ → ℝ}
    (hset : AbstractSetting h α β ε Δ ilo ihi lam)
    (hH1 : H1 h z α Δ) (hH2 : H2 h z β ε Δ ilo ihi lam) (hH3 : H3 h z)
    {d : ℝ} (hd : DeltaLowerBound α β ilo ihi d) :
    (∀ n : ℕ, ihi ≤ (n : ℤ) →
      ∃ v ∈ LimitingSubdiff h (z n),
        ‖v‖ ≤ Real.sqrt (((h (z ((n : ℤ) - ihi).toNat)).toReal -
            (h (z ((n : ℤ) + 1 - ilo).toNat)).toReal) / d) + ε n / β n) ∧
    (Tendsto (fun n => ε n / β n) atTop (𝓝 0) →
      ∀ zbar ∈ omega0 h z, (0 : EuclideanSpace ℝ (Fin P)) ∈ LimitingSubdiff h zbar) := by sorry

end FracPSG.Abstract
