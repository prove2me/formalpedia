-- Prove2me | Theorems.Thm_GoldenRatioVI_Fixed_energy_inequality
-- name    : GoldenRatioVI.Fixed.energy_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:57:40.460623+00:00
-- url     : https://prove2.me/theorems/52fc1436-26ee-4c4c-aeef-a7913356886d
-- title:
--   Eq. (14) — energy inequality for the fixed-step Golden Ratio Algorithm
-- statement:
--   Let $\mathcal E$ be a finite-dimensional real inner product space, $\varphi=\frac{\sqrt5+1}2$, and assume:
--
--   1. $g:\mathcal E\to(-\infty,+\infty]$ is proper, convex and lower semicontinuous (C2);
--   2. $F$ is monotone on $\operatorname{dom} g$ (C3) and $L$-Lipschitz on $\operatorname{dom} g$ with $L>0$;
--   3. $\lambda\in\big(0,\frac{\varphi}{2L}\big]$;
--   4. $(z^k)$, $(\bar z^k)$ is a run of the Golden Ratio Algorithm (6) with step $\lambda$ and $z^1\in\operatorname{dom} g$;
--   5. $z^*\in S$ is a solution of the variational inequality (1).
--
--   Then for every $k\ge2$
--   $$(1+\varphi)\|\bar z^{k+1}-z^*\|^2 + \frac\varphi2\|z^{k+1}-z^k\|^2 \;\le\; (1+\varphi)\|\bar z^k-z^*\|^2 + \frac\varphi2\|z^k-z^{k-1}\|^2 - \varphi\|z^k-\bar z^k\|^2.$$
--
--   The inequality says that a golden-ratio weighted energy is nonincreasing along the iterates and decreases by $\varphi\|z^k-\bar z^k\|^2$; boundedness of $(\bar z^k)$ and $\|z^k-\bar z^k\|\to0$ follow from it.
--
--   **Formalization Note** The range $k\ge2$ is the one where both prox steps (7) and (8) of the paper's proof are available ($z^k$ is itself a prox point). The hypothesis $z^1\in\operatorname{dom} g$ is not printed: the paper's $F$ is defined only on $\operatorname{dom} g$, so $F(z^1)$ in (6) presupposes it, and at $k=2$ the Lipschitz estimate for $\|F(z^2)-F(z^1)\|$ needs it. For $k\ge3$ it is not used. The Lipschitz condition is written as $\|F(u)-F(v)\|\le L\|u-v\|$ for $u,v\in\operatorname{dom} g$.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (Optimization Online 6598, 2018), p. 4, Eq. (14) (proof of Theorem 1)

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_GoldenRatioVI_Fixed_IsGRAALRun
open scoped goldenRatio

namespace GoldenRatioVI.Fixed

/-- Eq. (14), the energy inequality of the fixed-step Golden Ratio Algorithm: under (C2), (C3),
`F` `L`-Lipschitz on `dom g`, `λ ∈ (0, φ/(2L)]`, for a run of (6) with `z¹ ∈ dom g`, every
solution `z* ∈ S` and every `k ≥ 2`,
`(1+φ)‖z̄ᵏ⁺¹ - z*‖² + (φ/2)‖zᵏ⁺¹ - zᵏ‖²
   ≤ (1+φ)‖z̄ᵏ - z*‖² + (φ/2)‖zᵏ - zᵏ⁻¹‖² - φ‖zᵏ - z̄ᵏ‖²`. -/
theorem energy_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (F : E → E) (L lam : ℝ) (z zbar : ℕ → E)
    (hg : IsProperConvexLSC g) (hF : IsMonotoneOperatorOn F (effDom g))
    (hL : 0 < L) (hLip : ∀ u ∈ effDom g, ∀ v ∈ effDom g, ‖F u - F v‖ ≤ L * ‖u - v‖)
    (hlam : 0 < lam) (hlamL : lam ≤ φ / (2 * L))
    (hrun : IsGRAALRun g F lam z zbar) (hz1 : z 1 ∈ effDom g)
    (zs : E) (hzs : zs ∈ solutionSet g F) (k : ℕ) (hk : 2 ≤ k) :
    (1 + φ) * ‖zbar (k + 1) - zs‖ ^ 2 + φ / 2 * ‖z (k + 1) - z k‖ ^ 2 ≤
      (1 + φ) * ‖zbar k - zs‖ ^ 2 + φ / 2 * ‖z k - z (k - 1)‖ ^ 2
        - φ * ‖z k - zbar k‖ ^ 2 := by sorry

end GoldenRatioVI.Fixed
