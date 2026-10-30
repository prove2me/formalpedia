-- Prove2me | Theorems.Thm_NemirovskiProx_proposition_2_2
-- name    : NemirovskiProx.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:50:50.71274+00:00
-- url     : https://prove2.me/theorems/f54c1fde-d193-4f07-8a7d-9554e15406ef
-- title:
--   Proposition 2.2: convergence of the relaxed conceptual prox-method
-- statement:
--   Assume the standing assumptions of §2.1–2.2: $Z$ is a convex compact set in a Euclidean space $E$, $\|\cdot\|$ a norm on $E$, $F$ satisfies (2.1), and $\omega$ satisfies (2.2). Consider the relaxed conceptual prox-method from any $z_0\in Z$, in which the condition (2.9) is weakened to (2.11) with tolerances $\epsilon_t$.
--
--   1. If the relaxed algorithm terminates at a certain step $N$ according to rule (2.8), then $z_{N-1}$ solves the variational inequality:
--   $$\langle F(z_{N-1}),u-z_{N-1}\rangle\ge0\qquad\forall u\in Z. \tag{2.12}$$
--   2. If the relaxed algorithm does not terminate in the course of $N\ge1$ steps, then
--   $$\epsilon(z^N)\equiv\max_{u\in Z}\langle F(u),z^N-u\rangle\le\frac{\Theta(z_0)+\sum_{t=1}^N\epsilon_t}{\sum_{t=1}^N\gamma_t}. \tag{2.13}$$
--   3. If, in addition, the variational inequality comes from a convex-concave saddle point problem — $E=E_x\times E_y$ for Euclidean spaces $E_x,E_y$, $Z=X\times Y$ for convex compacts $X\subset E_x$, $Y\subset E_y$, and $F(x,y)=[f'_x(x,y);-f'_y(x,y)]$ for a continuously differentiable $f:X\times Y\to\mathbb R$ convex in $x\in X$ and concave in $y\in Y$ — then, with $z^N=(x^N,y^N)$,
--   $$\epsilon_f(z^N)\equiv\Big[\max_{y\in Y}f(x^N,y)-\min_{x\in X}\max_{y\in Y}f(x,y)\Big]+\Big[\max_{y\in Y}\min_{x\in X}f(x,y)-\min_{x\in X}f(x,y^N)\Big]\le\frac{\Theta(z_0)+\sum_{t=1}^N\epsilon_t}{\sum_{t=1}^N\gamma_t}. \tag{2.14}$$
--
--   This is the ergodic convergence guarantee of the prox-method; Theorem 3.2 specializes it to the basic implementation.
--
--   **Formalization Note** Part I of the Lean statement is (i) and (2.13) for every finite-dimensional real inner product space; Part II is (2.14). In (i), the run of $n=N-1$ non-terminating steps reaches $z_{N-1}$, which then passes the test (2.8).
--
--   Differences from the source:
--   - encoding: ‖·‖ is a norm on E and ‖ξ‖∗ = max_{z:‖z‖≤1}⟨ξ, z⟩ → a seminorm N on E with N x = 0 → x = 0, and ‖ξ‖∗ = sSup of ⟨ξ, z⟩ over N z ≤ 1; reason: a definite seminorm is a norm; Lean's ‖·‖ on E is the inner-product norm, so the paper's norm is a separate object; the supremum is attained on the compact unit ball of finite-dimensional E
--   - encoding: ω : Z → R continuously differentiable with derivative ω′, F : Z → E → ω, ω′, F are functions on all of E; ω′(z) is a gradient of ω at z within Z and ω′ is continuous on Z; reason: only the values on Z enter any statement; the paper's ω′ is such a gradient field and no interior point of Z is assumed
--   - encoding: argmin and max/min over compact sets → a predicate for the minimizer (IsProxPointOn) and sSup/sInf of images; reason: the minimizer exists and is unique by compactness and strong convexity, and every supremum/infimum is over a nonempty compact image of a continuous function, hence attained
--   - encoding: the relaxed CPM (p. 233, with (2.11) for (2.9)) not terminating in the course of N steps; step t = 1, …, N → IsRelaxedCPMRun: z 0 ∈ Z and for each t < n, z t fails (2.8), γs (t+1) > 0, w (t+1) ∈ Z, z (t+1) is the prox point of γs (t+1) F(w (t+1)) at z t, and (2.11) holds; reason: the paper's step t is t + 1 here, avoiding natural subtraction; same runs
--   - encoding: the relaxed algorithm terminates at step N according to (2.8) → a run of n non-terminating steps whose point z n satisfies the test (2.8); reason: N = n + 1 and z_{N−1} = z n; same situations
--   - encoding: N steps, N ≥ 1 (z^N and the bounds divide by N and by Σγt) → 1 ≤ n; reason: excludes only the undefined case N = 0
--   - encoding: E = Ex × Ey for Euclidean spaces Ex, Ey; Z = X × Y; F(x, y) = [f′x(x, y); −f′y(x, y)]; (x^N, y^N) the components of z^N → E = WithLp 2 (Ex × Ey) (inner product ⟨x, x′⟩ + ⟨y, y′⟩), Z = prodSet X Y, F = saddleOp fx fy, and the two components of ergodicAvg; reason: the Euclidean structure of the product used in the proof of (2.14), p. 236; same instances
--   - generalization: f : X × Y → R continuously differentiable → fx (x, y), fy (x, y) are gradients of f(·, y) within X and of f(x, ·) within Y, jointly continuous on X × Y; reason: only the partial gradients enter (through F); every continuously differentiable f has continuous partial gradients, so the source's case is included
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, Proposition 2.2, (2.11)–(2.14), p. 234

import Mathlib
import Definitions.Def_NemirovskiProx_dualNorm
import Definitions.Def_NemirovskiProx_IsLipMonotoneOn
import Definitions.Def_NemirovskiProx_IsDistGen
import Definitions.Def_NemirovskiProx_IsProxPointOn
import Definitions.Def_NemirovskiProx_stepGap
import Definitions.Def_NemirovskiProx_IsRelaxedCPMRun
import Definitions.Def_NemirovskiProx_Theta
import Definitions.Def_NemirovskiProx_viError
import Definitions.Def_NemirovskiProx_ergodicAvg
import Definitions.Def_NemirovskiProx_prodSet
import Definitions.Def_NemirovskiProx_saddleOp
import Definitions.Def_NemirovskiProx_IsSmoothConvexConcave
import Definitions.Def_NemirovskiProx_saddleGap

open scoped InnerProductSpace

universe u

namespace NemirovskiProx

/-- **Proposition 2.2: convergence of the relaxed conceptual prox-method, (2.12)–(2.14).**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), Proposition 2.2, p. 234: "Consider a "relaxed" version of CPM, where condition (2.9) is
weakened to (2.11). (i) If the relaxed algorithm terminates at a certain step N according to
rule (2.8), then zN−1 is a solution to the v.i. ⟨F(zN−1), u − zN−1⟩ ≥ 0 ∀u ∈ Z. (2.12)
(ii) If the relaxed algorithm does not terminate in the course of N steps, then ϵ(z^N) ≡
max_{u∈Z} ⟨F(u), z^N − u⟩ ≤ (Θ(z0) + Σ_{t=1}^N ϵt)/(Σ_{t=1}^N γt) (2.13). If, in addition, the
v.i. in question is associated with a convex-concave saddle point problem, [...] then ϵf(z^N)
≤ (Θ(z0) + Σ_{t=1}^N ϵt)/(Σ_{t=1}^N γt), (2.14) with Θ(z0) given by (2.13)."

Part I is (i) and (2.13) for every finite-dimensional real inner product space `E`, every
convex compact `Z`, every norm `N`, every `F` satisfying (2.1) and `ω` satisfying (2.2), and
every starting point `z 0 ∈ Z`. Part II is (2.14) for `E = E_x × E_y`, `Z = X × Y`,
`F = [f′_x; −f′_y]`.

**Formalization Note.** (i): the run of `n` non-terminating steps reaches `z n = z_{N−1}`
(`N = n + 1`), which passes the termination test (2.8). (ii): `1 ≤ n`. `E_x × E_y` is
`WithLp 2 (Ex × Ey)` (inner product `⟨x, x′⟩ + ⟨y, y′⟩`), `(x^N, y^N)` are the two components
of `z^N`, and `F` satisfies (2.1) as in the standing assumptions of §2.1. -/
theorem proposition_2_2 :
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      (Z : Set E) (N : Seminorm ℝ E) (α L : ℝ) (ω : E → ℝ) (ω' : E → E) (F : E → E),
      Convex ℝ Z → IsCompact Z → (∀ x, N x = 0 → x = 0) →
      IsDistGen Z N α ω ω' → IsLipMonotoneOn Z N L F →
      ∀ (γs εs : ℕ → ℝ) (z w : ℕ → E) (n : ℕ),
        (IsRelaxedCPMRun Z F ω ω' γs εs z w n →
          IsProxPointOn Z ω ω' (z n) (F (z n)) (z n) →
          ∀ u ∈ Z, 0 ≤ ⟪F (z n), u - z n⟫_ℝ) ∧
        (1 ≤ n → IsRelaxedCPMRun Z F ω ω' γs εs z w n →
          viError Z F (ergodicAvg γs w n) ≤
            (Theta Z ω ω' (z 0) + ∑ t ∈ Finset.Icc 1 n, εs t) / ∑ t ∈ Finset.Icc 1 n, γs t)) ∧
    (∀ {Ex Ey : Type u} [NormedAddCommGroup Ex] [InnerProductSpace ℝ Ex] [FiniteDimensional ℝ Ex]
      [NormedAddCommGroup Ey] [InnerProductSpace ℝ Ey] [FiniteDimensional ℝ Ey]
      (X : Set Ex) (Y : Set Ey) (f : Ex × Ey → ℝ) (fx : Ex × Ey → Ex) (fy : Ex × Ey → Ey)
      (N : Seminorm ℝ (WithLp 2 (Ex × Ey))) (α L : ℝ) (ω : WithLp 2 (Ex × Ey) → ℝ)
      (ω' : WithLp 2 (Ex × Ey) → WithLp 2 (Ex × Ey)),
      Convex ℝ X → IsCompact X → Convex ℝ Y → IsCompact Y →
      IsSmoothConvexConcave X Y f fx fy → (∀ x, N x = 0 → x = 0) →
      IsDistGen (prodSet X Y) N α ω ω' → IsLipMonotoneOn (prodSet X Y) N L (saddleOp fx fy) →
      ∀ (γs εs : ℕ → ℝ) (z w : ℕ → WithLp 2 (Ex × Ey)) (n : ℕ), 1 ≤ n →
        IsRelaxedCPMRun (prodSet X Y) (saddleOp fx fy) ω ω' γs εs z w n →
        saddleGap X Y f (WithLp.ofLp (ergodicAvg γs w n)).1 (WithLp.ofLp (ergodicAvg γs w n)).2 ≤
          (Theta (prodSet X Y) ω ω' (z 0) + ∑ t ∈ Finset.Icc 1 n, εs t) /
            ∑ t ∈ Finset.Icc 1 n, γs t) := by sorry

end NemirovskiProx
