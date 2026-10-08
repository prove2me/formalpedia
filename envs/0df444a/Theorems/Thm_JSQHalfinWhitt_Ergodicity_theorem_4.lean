-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Ergodicity_theorem_4
-- name    : JSQHalfinWhitt.Ergodicity.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:23.142148+00:00
-- url     : https://prove2.me/theorems/75b75c2e-d7f2-4c12-904d-86a7cf0634d6
-- title:
--   Theorem 4 — the JSQ diffusion limit admits a Foster–Lyapunov function: G_Y V ≤ −cV + d·1_K
-- statement:
--   Let $\beta>0$ and let $G_Y$ be the generator of the diffusion limit of the join-the-shortest-queue model in the Halfin–Whitt regime, acting on $f\in C^2(\Omega)$ with $f_1(0,x_2)=f_2(0,x_2)$ by
--   $$G_Yf(x)=(-x_1+x_2-\beta)f_1(x)-x_2f_2(x)+f_{11}(x),\qquad x\in\Omega=(-\infty,0]\times[0,\infty).$$
--   Then there exist constants $c>0$ and $d>0$, a compact set $K\subset\mathbb R^2$ and a function $V\in C^2(\Omega)$ such that
--
--   1. $V(x)\ge1$ for all $x\in\Omega$;
--   2. $V(x)\to\infty$ as $|x|\to\infty$ within $\Omega$;
--   3. $V_1(0,x_2)=V_2(0,x_2)$ for all $x_2\ge0$;
--   4. for every $x\in\Omega$,
--   $$G_YV(x)\le-cV(x)+d\,1(x\in K).\qquad(5.2)$$
--
--   The constants $c,d$, the set $K$ and the function $V$ depend only on $\beta$. Combined with the Down–Meyn–Tweedie criterion, (5.2) yields positive recurrence and exponential ergodicity of the diffusion (Theorem 3 and Corollary 1 of the paper).
--
--   **Formalization Note** $G_Y$ is the generator formula on p. 16, which the paper identifies with the extended generator of the process (2.1) for $C^2(\Omega)$ functions satisfying the reflection condition; the process itself is not constructed. Membership $V\in C^2(\Omega)$ (`ContDiffOn ℝ 2 V Ω`) is part of the conclusion: the theorem applies $G_Y$ to $V$, which needs $V$ in that class, and it rules out a $V$ whose derivatives within $\Omega$ do not exist and default to $0$. "$V(x)\to\infty$ as $|x|\to\infty$" is: for every $M$ there is $R$ with $V(x)\ge M$ for $x\in\Omega$, $\|x\|\ge R$ (sup norm on `ℝ × ℝ`, equivalent to the Euclidean norm here). Partials are one-sided on $\partial\Omega$. All constants are existential after $\beta$, and the statement involves no $n$.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 16, Theorem 4, (5.2); G_Y formula p. 16

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Ergodicity_Operators

namespace JSQHalfinWhitt.Ergodicity

/-- Theorem 4, p. 16: a Foster–Lyapunov drift condition (5.2) for the generator `G_Y` of the JSQ
diffusion limit. For every `β > 0` there are `c, d > 0`, a compact `K` and `V ∈ C²(Ω)` with `V ≥ 1` on
`Ω`, `V(x) → ∞` as `|x| → ∞` within `Ω`, and `V₁(0, x₂) = V₂(0, x₂)`, such that
`G_Y V(x) ≤ −c V(x) + d 1(x ∈ K)` for every `x ∈ Ω`. -/
theorem theorem_4 (β : ℝ) (hβ : 0 < β) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∃ K : Set (ℝ × ℝ), IsCompact K ∧
      ∃ V : ℝ × ℝ → ℝ, ContDiffOn ℝ 2 V JSQHalfinWhitt.Tightness.Omega ∧ (∀ x ∈ JSQHalfinWhitt.Tightness.Omega, 1 ≤ V x) ∧
        (∀ M : ℝ, ∃ R : ℝ, ∀ x ∈ JSQHalfinWhitt.Tightness.Omega, R ≤ ‖x‖ → M ≤ V x) ∧
        (∀ x2 : ℝ, 0 ≤ x2 → d1 V (0, x2) = d2 V (0, x2)) ∧
        ∀ x ∈ JSQHalfinWhitt.Tightness.Omega, genY β V x ≤ -c * V x + d * K.indicator (fun _ => (1 : ℝ)) x := by sorry

end JSQHalfinWhitt.Ergodicity
