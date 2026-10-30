-- Prove2me | Theorems.Thm_NemirovskiProx_theorem_3_2_basic_implementation
-- name    : NemirovskiProx.theorem_3_2_basic_implementation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:35:47.808114+00:00
-- url     : https://prove2.me/theorems/6439a6ae-4d1b-4a15-b5ff-79792596575a
-- title:
--   Theorem 3.2: two inner iterations suffice, and the $O(1/N)$ bounds (3.9)–(3.10)
-- statement:
--   Assume the standing assumptions of §2.1–2.2: $Z$ is a convex compact set in a Euclidean space $E$, $\|\cdot\|$ a norm on $E$ with dual norm $\|\cdot\|_*$, $F$ satisfies (2.1) with constant $L>0$, and $\omega$ is continuously differentiable and $\alpha$-strongly convex on $Z$ (2.2). Let the starting point $z_0$ be the minimizer of $\omega$ on $Z$ (Remark 2.3), and run the basic implementation (3.2)–(3.4) with $\gamma=\alpha/(\sqrt2L)$. Then:
--
--   1. the basic implementation ensures (3.4), and thus (2.11) with $\epsilon_t=0$, in no more than two inner iterations; consequently, in every run of $N\ge1$ non-terminating steps, $s_t\le2$ for every $t$ and the computational price of $z^N$ is at most $2N$ computations of $F$ and $2N$ auxiliary problems ($\sum_{t=1}^Ns_t\le2N$);
--   2. the error bound (2.13) becomes
--   $$\epsilon(z^N)\le\frac{\sqrt2\,\Theta(z_0)\,L}{\alpha N}; \tag{3.9}$$
--   3. if the variational inequality comes from a convex-concave saddle point problem ($E=E_x\times E_y$, $Z=X\times Y$ for convex compacts $X$, $Y$, $F=[f'_x;-f'_y]$ for a continuously differentiable $f$ convex in $x$ and concave in $y$), the error bound (2.14) becomes
--   $$\epsilon_f(z^N)\le\frac{\sqrt2\,\Theta(z_0)\,L}{\alpha N}. \tag{3.10}$$
--
--   This is the paper's main result: an implementable prox-method (mirror-prox) whose error decays as $O(1/N)$ for Lipschitz continuous monotone operators and smooth convex-concave saddle point problems, at the cost of at most two operator evaluations per step, for an arbitrary norm and an arbitrary strongly convex distance-generating function.
--
--   **Formalization Note** Part I of the Lean statement is clause 1 (as (A): from any $z\in Z$ failing (2.8), (3.4) holds at the first or second inner iteration; and (B): for every run, $s_t\le2$, the price, and (3.9)); Part II is (3.10). The stepsize is written out as $\alpha/(\sqrt2L)$.
--
--   Differences from the source:
--   - encoding: ‖·‖ is a norm on E and ‖ξ‖∗ = max_{z:‖z‖≤1}⟨ξ, z⟩ → a seminorm N on E with N x = 0 → x = 0, and ‖ξ‖∗ = sSup of ⟨ξ, z⟩ over N z ≤ 1; reason: a definite seminorm is a norm; Lean's ‖·‖ on E is the inner-product norm, so the paper's norm is a separate object; the supremum is attained on the compact unit ball of finite-dimensional E
--   - encoding: ω : Z → R continuously differentiable with derivative ω′, F : Z → E → ω, ω′, F are functions on all of E; ω′(z) is a gradient of ω at z within Z and ω′ is continuous on Z; reason: only the values on Z enter any statement; the paper's ω′ is such a gradient field and no interior point of Z is assumed
--   - encoding: argmin and max/min over compact sets → a predicate for the minimizer (IsProxPointOn) and sSup/sInf of images; reason: the minimizer exists and is unique by compactness and strong convexity, and every supremum/infimum is over a nonempty compact image of a continuous function, hence attained
--   - encoding: γ = α/(√2L) with L the constant of (2.1) → 0 < L assumed; reason: γ is undefined at L = 0; with Lean's division the L = 0 statement is false (Z = [−1, 1], F ≡ 1, ω = z²/2, z₀ = 0 give γ = 0, ε(z^N) = 1 > 0), so the hypothesis excludes only the undefined case
--   - encoding: N steps, N ≥ 1 (z^N and the bounds divide by N and by Σγt) → 1 ≤ n; reason: excludes only the undefined case N = 0
--   - encoding: N non-terminating steps t = 1, …, N of the basic implementation (3.2)–(3.4), inner iterates w_{t,s} → IsBasicImplRun: z 0 ∈ Z and for each t < n, z t fails (2.8), inner iterates v with v 0 = z t and v (j+1) the prox point of γF(v j) at z t, w (t+1) = v (s (t+1) − 1), z (t+1) = v (s (t+1)); reason: the paper's step t is t + 1 here and w_{t,s} is v s, avoiding natural subtraction; same runs
--   - reading: s_t is “the corresponding value of s”, the s at which (3.4) is met → s_t is the first s ≥ 1 at which (3.4) holds (IsBasicImplRun), and clause (A) says (3.4) holds at s = 1 or at s = 2 from any z ∈ Z failing (2.8); reason: the iteration runs “until the condition is met”, so it stops at the first such s
--   - reading: the computational price of z^N does not exceed 2N computations of F(·) and 2N auxiliary problems (1.6) → s_t ≤ 2 for every t and Σ_{t=1}^N s_t ≤ 2N; reason: inner iteration s of step t computes F(w_{t,s−1}) once and solves one problem (1.6)
--   - encoding: (3.4) “and thus (2.11) with ϵt = 0” → (3.4) at s_t, which the run contains; (2.11) is not restated; reason: with w_t = w_{t,s_t−1} and z_t = w_{t,s_t}, (2.11) with ϵt = 0 is literally (3.4)
--   - encoding: E = Ex × Ey for Euclidean spaces Ex, Ey; Z = X × Y; F(x, y) = [f′x(x, y); −f′y(x, y)]; (x^N, y^N) the components of z^N → E = WithLp 2 (Ex × Ey) (inner product ⟨x, x′⟩ + ⟨y, y′⟩), Z = prodSet X Y, F = saddleOp fx fy, and the two components of ergodicAvg; reason: the Euclidean structure of the product used in the proof of (2.14), p. 236; same instances
--   - generalization: f : X × Y → R continuously differentiable → fx (x, y), fy (x, y) are gradients of f(·, y) within X and of f(x, ·) within Y, jointly continuous on X × Y; reason: only the partial gradients enter (through F); every continuously differentiable f has continuous partial gradients, so the source's case is included
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, Theorem 3.2, (3.9)–(3.10), p. 239; standing assumptions §2.1–2.2, p. 232, Remark 2.3, p. 236, basic implementation (3.2)–(3.4), p. 237

import Mathlib
import Definitions.Def_NemirovskiProx_dualNorm
import Definitions.Def_NemirovskiProx_IsLipMonotoneOn
import Definitions.Def_NemirovskiProx_IsDistGen
import Definitions.Def_NemirovskiProx_IsProxPointOn
import Definitions.Def_NemirovskiProx_stepGap
import Definitions.Def_NemirovskiProx_IsBasicImplRun
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

/-- **Theorem 3.2: the basic implementation needs at most two inner iterations per step, and
(3.9)–(3.10).**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), Theorem 3.2, p. 239: "Assume that F satisfies (2.1). Then the basic implementation
ensures relation (3.4) (and thus (2.11) with ϵt = 0) in no more than two inner iterations.
Thus, with the basic implementation, the error bounds (2.13) and (2.14) become, respectively,
ϵ(z^N) ≤ √2Θ(z0)L/(αN) (3.9) and ϵf(z^N) ≤ √2Θ(z0)L/(αN), (3.10) while the "computational price"
of z^N does not exceed 2N computations of F(·) and solving 2N auxiliary problems (1.6)."

Standing assumptions: §2.1–2.2, p. 232 (`Z` convex compact in a Euclidean space `E`, `N` a norm,
`F` satisfies (2.1), `ω` satisfies (2.2)); Remark 2.3, p. 236 (`z₀` minimizes `ω` on `Z`); the
basic implementation (3.2)–(3.4), p. 237, with `γ = α/(√2 L)`.

Part I, for a general v.i.: (A) at a point `z ∈ Z` failing (2.8), (3.4) holds at the first or
the second inner iteration; (B) for every run of `n ≥ 1` non-terminating steps, every `s_t ≤ 2`,
`Σ_{t=1}^n s_t ≤ 2n` (the price), and (3.9). Part II is (3.10) for the saddle point case
`E = E_x × E_y`, `Z = X × Y`, `F = [f′_x; −f′_y]`.

**Formalization Note.** `γ` is written out as `α / (√2 * L)`. `0 < L` is assumed because (3.2)
divides by `L`. The price is read as `Σ s_t ≤ 2n`: inner iteration `s` computes `F(w_{t,s−1})`
once and solves one problem (1.6). `E_x × E_y` is `WithLp 2 (Ex × Ey)`; `(x^N, y^N)` are the
two components of `z^N`. -/
theorem theorem_3_2_basic_implementation :
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      (Z : Set E) (N : Seminorm ℝ E) (α L : ℝ) (ω : E → ℝ) (ω' : E → E) (F : E → E),
      Convex ℝ Z → IsCompact Z → (∀ x, N x = 0 → x = 0) →
      IsDistGen Z N α ω ω' → IsLipMonotoneOn Z N L F → 0 < L →
      (∀ z ∈ Z, ¬ IsProxPointOn Z ω ω' z (F z) z → ∀ w₁ w₂ : E,
          IsProxPointOn Z ω ω' z ((α / (Real.sqrt 2 * L)) • F z) w₁ →
          IsProxPointOn Z ω ω' z ((α / (Real.sqrt 2 * L)) • F w₁) w₂ →
          stepGap ω ω' z z w₁ ((α / (Real.sqrt 2 * L)) • F z) ≤ 0 ∨
            stepGap ω ω' z w₁ w₂ ((α / (Real.sqrt 2 * L)) • F w₁) ≤ 0) ∧
      (∀ (z w : ℕ → E) (s : ℕ → ℕ) (n : ℕ), 1 ≤ n →
          IsBasicImplRun Z F ω ω' (α / (Real.sqrt 2 * L)) z w s n →
          (∀ v ∈ Z, ω (z 0) ≤ ω v) →
          (∀ t ∈ Finset.Icc 1 n, s t ≤ 2) ∧
            ∑ t ∈ Finset.Icc 1 n, s t ≤ 2 * n ∧
            viError Z F (ergodicAvg (fun _ => (α / (Real.sqrt 2 * L))) w n) ≤
              Real.sqrt 2 * Theta Z ω ω' (z 0) * L / (α * (n : ℝ)))) ∧
    (∀ {Ex Ey : Type u} [NormedAddCommGroup Ex] [InnerProductSpace ℝ Ex] [FiniteDimensional ℝ Ex]
      [NormedAddCommGroup Ey] [InnerProductSpace ℝ Ey] [FiniteDimensional ℝ Ey]
      (X : Set Ex) (Y : Set Ey) (f : Ex × Ey → ℝ) (fx : Ex × Ey → Ex) (fy : Ex × Ey → Ey)
      (N : Seminorm ℝ (WithLp 2 (Ex × Ey))) (α L : ℝ) (ω : WithLp 2 (Ex × Ey) → ℝ)
      (ω' : WithLp 2 (Ex × Ey) → WithLp 2 (Ex × Ey)),
      Convex ℝ X → IsCompact X → Convex ℝ Y → IsCompact Y →
      IsSmoothConvexConcave X Y f fx fy → (∀ x, N x = 0 → x = 0) →
      IsDistGen (prodSet X Y) N α ω ω' → IsLipMonotoneOn (prodSet X Y) N L (saddleOp fx fy) →
      0 < L →
      ∀ (z w : ℕ → WithLp 2 (Ex × Ey)) (s : ℕ → ℕ) (n : ℕ), 1 ≤ n →
        IsBasicImplRun (prodSet X Y) (saddleOp fx fy) ω ω' (α / (Real.sqrt 2 * L)) z w s n →
        (∀ v ∈ prodSet X Y, ω (z 0) ≤ ω v) →
        saddleGap X Y f (WithLp.ofLp (ergodicAvg (fun _ => (α / (Real.sqrt 2 * L))) w n)).1
            (WithLp.ofLp (ergodicAvg (fun _ => (α / (Real.sqrt 2 * L))) w n)).2 ≤
          Real.sqrt 2 * Theta (prodSet X Y) ω ω' (z 0) * L / (α * (n : ℝ))) := by sorry

end NemirovskiProx
