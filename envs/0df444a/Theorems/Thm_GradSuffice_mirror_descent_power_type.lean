-- Prove2me | Theorems.Thm_GradSuffice_mirror_descent_power_type
-- name    : GradSuffice.mirror_descent_power_type
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:23:16.890043+00:00
-- url     : https://prove2.me/theorems/578c1341-022b-47ca-9e3e-23a751d55d22
-- title:
--   Eq. (2), p.5 — Mirror Descent with a $(C,q)$-uniformly convex regularizer: $T(\varepsilon)=O(\varepsilon^{-q})$
-- statement:
--   Let $X$ be a Banach space with unit ball $B$, and let $R:B\to[0,\infty)$ be lower semicontinuous, convex, 1-bounded ($0\le R\le1$) and **$(C,q)$-uniformly convex** for some $C>0$, $q\ge2$:
--   $$R\Big(\frac{w_1+w_2}2\Big)\le\frac12R(w_1)+\frac12R(w_2)-\Big(\frac1C\Big)^q\Big\|\frac{w_1-w_2}2\Big\|^q\qquad(w_1,w_2\in B).$$
--
--   **Mirror Descent guarantee.** With learning rate $\eta=\varepsilon^{q-1}/q$, Mirror Descent with regularizer $R$ satisfies $f(\bar w_T)-f(w)\le O\big(1/(\varepsilon^{q-1}T)+\varepsilon\big)$ for every $w\in B$, and one more query at $\bar w_T$ makes it the output. Hence there is a constant $A>0$ depending only on $C$ and $q$ such that for every $0<\varepsilon\le1$ some deterministic first-order algorithm on $B$ with at most
--   $$T\le A\,\varepsilon^{-q}$$
--   queries outputs a last query $w_T$ with $f(w_T)-\inf_Bf\le\varepsilon$ for every objective and every valid oracle.
--
--   This is the implication 5 → 1 of Theorem 1, with the deterministic algorithm giving deterministic optimizability.
--
--   Differences from the source:
--   - encoding: f(w̄_T) − f(w) ≤ O(1/(ε^{q−1}T) + ε), plus one query at w̄_T → ∃ A(C, q) > 0: for 0 < ε ≤ 1 a deterministic algorithm with T ≤ A ε^{−q} queries has last query within ε of inf_B f; reason: the O(·) constant depends on C and q (R is 1-bounded); choosing T of order ε^{−q} and rescaling ε gives this form
--   - encoding: R : B → [0, ∞) bounded, 1-bounded; (C, q)-uniform convexity → 0 ≤ R ≤ 1 on B; NondualOpt.IsUnifConvexOn B R ((1/(2C))^q) q; reason: ‖(w₁ − w₂)/2‖^q = (1/2)^q ‖w₁ − w₂‖^q
--   - reading: every valid first-order oracle ("O receives a point w ∈ W and returns a pair (f(w), ξ)") → every fixed subgradient selection w ↦ g(w); reason: p.4 defines the oracle as a map from the queried point to the answer
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §2, Eq. (2) and the power-type paragraph, pp.4–5

import Mathlib
import Definitions.Def_NondualOpt_IsUnifConvexOn
import Definitions.Def_GradSuffice_IsValidOracle
import Definitions.Def_GradSuffice_DetAlg_lastQuery

namespace GradSuffice

/-- **Mirror Descent with a regularizer of power type (Eq. (2)).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §2, pp.4–5: "For the Mirror
Descent guarantees, assume that `X` is a Banach space. The regularizer `R : B → [0, ∞)` is bounded,
lower semicontinuous, and uniformly convex […] By imposing further structure on the modulus `ψ`, one
can obtain explicit optimization guarantees. For example, `ψ(a) = a^q` with `q ≥ 2` corresponds to
uniform convexity of power type `q`. A 1-bounded convex function `R : B → ℝ` is said to be
`(C, q)`-uniformly convex if, for every `w₁, w₂ ∈ B`, `R((w₁+w₂)/2) ≤ (1/2)R(w₁) + (1/2)R(w₂) −
(1/C)^q ‖(w₁−w₂)/2‖^q`. If `ψ(a) = a^q`, choose the learning rate `η = ε^{q−1}/q`. […] the preceding bound
yields `f(w̄_T) − f(w) ≤ O(1/(ε^{q−1}T) + ε)`." and "Querying `w̄_T` once more before returning it
enforces our output convention at a cost of one additional oracle call."

**Formalization Note.** The `O(·)` becomes a constant `A > 0` depending only on `C` and `q`, chosen
before the space: for `0 < ε ≤ 1` some deterministic algorithm with at most `A ε^{−q}` queries
(including the final one) has last query within `ε` of `inf_B f` for every objective and every
valid oracle. `(C, q)`-uniform convexity is `NondualOpt.IsUnifConvexOn B R ((1/(2C))^q) q`;
"1-bounded" with values in `[0, ∞)` is `0 ≤ R ≤ 1` on `B`. -/
theorem mirror_descent_power_type :
    ∀ C q : ℝ, 0 < C → 2 ≤ q → ∃ A : ℝ, 0 < A ∧
      ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (R : X → ℝ),
        LowerSemicontinuousOn R (Metric.closedBall (0 : X) 1) → ConvexOn ℝ (Metric.closedBall (0 : X) 1) R →
        (∀ w ∈ Metric.closedBall (0 : X) 1, 0 ≤ R w ∧ R w ≤ 1) →
        NondualOpt.IsUnifConvexOn (Metric.closedBall (0 : X) 1) R ((1 / (2 * C)) ^ q) q →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          ∃ T : ℕ, 0 < T ∧ (T : ℝ) ≤ A * ε ^ (-q) ∧ ∃ alg : DetAlg X (Metric.closedBall (0 : X) 1) T,
            ∀ (F : Objective X (Metric.closedBall (0 : X) 1)) (g : X → StrongDual ℝ X), IsValidOracle F g →
              F.f (alg.lastQuery F.f g) - sInf (F.f '' Metric.closedBall (0 : X) 1) ≤ ε := by sorry

end GradSuffice
