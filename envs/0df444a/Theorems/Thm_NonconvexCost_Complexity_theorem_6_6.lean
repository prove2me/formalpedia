-- Prove2me | Theorems.Thm_NonconvexCost_Complexity_theorem_6_6
-- name    : NonconvexCost.Complexity.theorem_6_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:45.700324+00:00
-- url     : https://prove2.me/theorems/bf92e90a-ede7-469e-b111-eb11dbed5c50
-- title:
--   Theorem 6.6, pp. 17–18 (corrected phase count) — Algorithm 4.1 finds a small Goldstein subgradient within an explicit number of oracle calls
-- statement:
--   **Theorem 6.6 (complexity of minimization), with the phase count corrected.** Let $X$ be a real inner product space, let $\delta,\epsilon>0$, let $C\subset X$ be convex, let $f$ be bounded below on $C$, and let $G\colon X^2\to X$ be an $L$-bounded directional subgradient map for $f$ on $C$. Let $x_0\in C$ satisfy
--   $$x\in C,\ f(x)\le f(x_0),\ |y|\le\delta\ \Longrightarrow\ x+y\in C,$$
--   and suppose $f$ has finite nonconvexity modulus $\Lambda(\delta)$. Start Algorithm 4.1 (nonsmooth minimization, with the bisection line search) at $x_0$ with any Goldstein subgradient $g_0\in\partial_\delta f(x_0)$. Then within at most
--   $$\Big(\Big\lfloor\frac{3(f(x_0)-\inf_C f)}{\delta\epsilon}\Big\rfloor+1\Big)\cdot\frac{16L^2}{\epsilon^2}\cdot\Big(1+\Big\lfloor\frac{12\Lambda(\delta)}{\epsilon}\Big\rfloor\Big)$$
--   calls to Oracle 2.5 the algorithm stops at a point $x\in X$ with a Goldstein subgradient $g\in\partial_\delta f(x)$ satisfying $|g|\le\epsilon$.
--
--   For weakly convex and difference-of-convex objectives $\Lambda(\delta)$ is bounded, and the bound becomes the $O(\epsilon^{-4})$ and $O(\epsilon^{-5})$-type complexities of the paper, achieved by a deterministic method without any semismoothness assumption.
--
--   **Formalization Note** *Corrected.* The paper prints the first factor as $\lceil3(f(x_0)-\min f)/(\delta\epsilon)\rceil$. That bound is $0$ when $f(x_0)=\min f$, but it fails there: on $X=C=\mathbb R$ with $f\equiv0$, $L=2$, $\epsilon=\delta=1$, $G(x,e)=0$ for $e\ne0$ and $G(x,0)=2$, the run started with $g_0=G(x_0,0)$ has $|g_0|>\epsilon$ and needs an oracle call. The proof on p. 10 allows at most $\lfloor3(f(x_0)-\inf f)/(\delta\epsilon)\rfloor$ reductions, hence one more phase, which is the count used here. "$\min f$" is the infimum of $f$ over $C$. The count includes every oracle call (trial points, bisection midpoints, re-initialisations $G(x',0)$), which is stricter than the paper's proof, and the bound still holds. $f$ is a function on $X$, constrained only on $C$: the oracle identity is required at points of $C$ along directions that stay in $C$ for small steps. The bisection test uses $h(l)+h(r)$ (Algorithm 3.1 prints $f(l)+f(r)$).
-- source:
--   Kong, Lewis, The cost of nonconvexity in deterministic nonsmooth optimization, arXiv:2210.00652v2, pp. 17–18, Theorem 6.6 (corrected phase count)

import Mathlib
import Definitions.Def_NonconvexCost_Complexity_Setting
import Definitions.Def_NonconvexCost_Complexity_Algorithm

namespace NonconvexCost.Complexity

theorem theorem_6_6 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (δ ε L : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (C : Set X) (hC : Convex ℝ C) (f : X → ℝ)
    (hbdd : BddBelow (f '' C)) (G : X → X → X) (hG : IsDirSubgradMapOn f G C)
    (hL : IsLBounded G L) (x0 : X) (hx0 : x0 ∈ C)
    (hsub : ∀ x ∈ C, f x ≤ f x0 → ∀ y : X, ‖y‖ ≤ δ → x + y ∈ C)
    (hΛ : nonconvexityModulus f C δ ≠ ⊤) (g0 : X) (hg0 : g0 ∈ goldstein G δ x0) :
    ∃ n : ℕ,
      (n : ℝ) ≤ ((⌊3 * (f x0 - sInf (f '' C)) / (δ * ε)⌋₊ : ℝ) + 1) * (16 * L ^ 2 / ε ^ 2) *
          (1 + ⌊12 * (nonconvexityModulus f C δ).toReal / ε⌋₊) ∧
        IsDone ε (run f G δ ε x0 g0 n) ∧
        (run f G δ ε x0 g0 n).g ∈ goldstein G δ (run f G δ ε x0 g0 n).x := by sorry

end NonconvexCost.Complexity
