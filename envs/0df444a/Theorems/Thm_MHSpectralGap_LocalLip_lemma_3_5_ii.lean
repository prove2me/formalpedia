-- Prove2me | Theorems.Thm_MHSpectralGap_LocalLip_lemma_3_5_ii
-- name    : MHSpectralGap.LocalLip.lemma_3_5_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:37.836986+00:00
-- url     : https://prove2.me/theorems/91a25b77-3e4d-4e64-bde5-7dde3b615696
-- title:
--   Lemma 3.5 (2), p. 22 — two-sided comparison of d̄(x, y) with ‖x − y‖/ε when d̄(x, y) < 1
-- statement:
--   Let $H$ be a real inner product space, $\eta,\varepsilon>0$, and let $\bar d$ be the weighted path distance (3.6) with $J=\varepsilon\exp(-\eta((\|x\|\vee\|y\|-\varepsilon)\vee0))$. For all $x,y\in H$ with $\bar d(x,y)<1$,
--
--   $$\bar d(x,y)\le\frac{\|x-y\|}{\varepsilon}\exp\bigl(\eta(\|x\|\vee\|y\|)\bigr)\qquad\text{and}\qquad\frac{\|x-y\|}{\varepsilon}\exp\bigl(\eta\,((\|x\|\vee\|y\|-J)\vee0)\bigr)\le\bar d(x,y).$$
--
--   Up to the factor $e^{\eta J}\le e^{\eta\varepsilon}$, the distance $\bar d(x,y)$ is therefore $\|x-y\|e^{\eta(\|x\|\vee\|y\|)}/\varepsilon$ for close points. This is what turns the norm estimates of the pCN step into estimates for $d$.
--
--   **Formalization Note** $\bar d$ is valued in $[0,\infty]$ and both sides are compared there; the hypothesis $\bar d(x,y)<1$ is applied to both inequalities, as the page states it after both.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 22, Lemma 3.5 (2)

import Mathlib
import Definitions.Def_MHSpectralGap_LocalLip_PathMetric

namespace MHSpectralGap.LocalLip

/-- Lemma 3.5 (2), p. 22: for points with `d̄(x, y) < 1`,
`d̄(x, y) ≤ (‖x − y‖/ε) exp(η(‖x‖ ∨ ‖y‖))` and
`(‖x − y‖/ε) exp(η((‖x‖ ∨ ‖y‖ − J) ∨ 0)) ≤ d̄(x, y)`. -/
theorem lemma_3_5_ii {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) (x y : H) (hd : dBarE η ε x y < 1) :
    dBarE η ε x y ≤ ENNReal.ofReal (‖x - y‖ / ε * Real.exp (η * max ‖x‖ ‖y‖)) ∧
      ENNReal.ofReal (‖x - y‖ / ε * Real.exp (η * max (max ‖x‖ ‖y‖ - Jlen η ε x y) 0)) ≤
        dBarE η ε x y := by sorry

end MHSpectralGap.LocalLip
