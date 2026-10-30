-- Prove2me | Theorems.Thm_NemirovskiProx_eq_2_16_summed
-- name    : NemirovskiProx.eq_2_16_summed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:49:53.848458+00:00
-- url     : https://prove2.me/theorems/c7f95aae-794b-4fe6-ad44-d7b567a181a8
-- title:
--   (2.16): the summed inequality of the relaxed conceptual prox-method
-- statement:
--   Under the assumptions of (2.15), for every $u\in Z$:
--   $$\begin{aligned}\sum_{t=1}^N\gamma_t\langle F(w_t),w_t-u\rangle&\le H_u(z_0)-H_u(z_N)+\sum_{t=1}^N\epsilon_t\\&=\big[\langle z_0-u,\omega'(z_0)\rangle-\omega(z_0)\big]+\big[\langle u-z_N,\omega'(z_N)\rangle+\omega(z_N)\big]+\sum_{t=1}^N\epsilon_t\\&\le\omega(u)-\langle\omega'(z_0),u-z_0\rangle-\omega(z_0)+\sum_{t=1}^N\epsilon_t\le\Theta(z_0)+\sum_{t=1}^N\epsilon_t,\end{aligned}\tag{2.16}$$
--   where $\langle u-z_N,\omega'(z_N)\rangle+\omega(z_N)\le\omega(u)$. Every link of this chain is asserted, including the end-to-end bound by $\Theta(z_0)+\sum_t\epsilon_t$.
--
--   Combined with the monotonicity of $F$, (2.16) yields the error bounds (2.13) and (2.14).
--
--   Differences from the source:
--   - encoding: ‖·‖ is a norm on E and ‖ξ‖∗ = max_{z:‖z‖≤1}⟨ξ, z⟩ → a seminorm N on E with N x = 0 → x = 0, and ‖ξ‖∗ = sSup of ⟨ξ, z⟩ over N z ≤ 1; reason: a definite seminorm is a norm; Lean's ‖·‖ on E is the inner-product norm, so the paper's norm is a separate object; the supremum is attained on the compact unit ball of finite-dimensional E
--   - encoding: ω : Z → R continuously differentiable with derivative ω′, F : Z → E → ω, ω′, F are functions on all of E; ω′(z) is a gradient of ω at z within Z and ω′ is continuous on Z; reason: only the values on Z enter any statement; the paper's ω′ is such a gradient field and no interior point of Z is assumed
--   - encoding: argmin and max/min over compact sets → a predicate for the minimizer (IsProxPointOn) and sSup/sInf of images; reason: the minimizer exists and is unique by compactness and strong convexity, and every supremum/infimum is over a nonempty compact image of a continuous function, hence attained
--   - encoding: the relaxed CPM (p. 233, with (2.11) for (2.9)) not terminating in the course of N steps; step t = 1, …, N → IsRelaxedCPMRun: z 0 ∈ Z and for each t < n, z t fails (2.8), γs (t+1) > 0, w (t+1) ∈ Z, z (t+1) is the prox point of γs (t+1) F(w (t+1)) at z t, and (2.11) holds; reason: the paper's step t is t + 1 here, avoiding natural subtraction; same runs
--   - generalization: N ≥ 1 steps → every n : ℕ, including n = 0; reason: at n = 0 all sums are empty and each link holds trivially; the source's N ≥ 1 is included
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, proof of Proposition 2.2, eq. (2.16), p. 235

import Mathlib
import Definitions.Def_NemirovskiProx_dualNorm
import Definitions.Def_NemirovskiProx_IsLipMonotoneOn
import Definitions.Def_NemirovskiProx_IsDistGen
import Definitions.Def_NemirovskiProx_IsProxPointOn
import Definitions.Def_NemirovskiProx_stepGap
import Definitions.Def_NemirovskiProx_IsRelaxedCPMRun
import Definitions.Def_NemirovskiProx_legendre
import Definitions.Def_NemirovskiProx_Hfun
import Definitions.Def_NemirovskiProx_Theta

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **(2.16): the summed inequality for the relaxed conceptual prox-method.**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), proof of Proposition 2.2, (2.16), p. 235: "∀(u ∈ Z): Σ_{t=1}^N γt⟨F(wt), wt − u⟩ ≤
Hu(z0) − Hu(zN) + Σ_{t=1}^N ϵt = [⟨z0 − u, ω′(z0)⟩ − ω(z0)] + [⟨u − zN, ω′(zN)⟩ + ω(zN)] +
Σ_{t=1}^N ϵt ≤ ω(u) − ⟨ω′(z0), u − z0⟩ − ω(z0) + Σ_{t=1}^N ϵt ≤ Θ(z0) + Σ_{t=1}^N ϵt."

Every link of the chain is stated, for every `u ∈ Z`: (1) the first inequality; (2) the
identity for `H_u(z₀) − H_u(z_N)`; (3) the underbrace `[⟨u − z_N, ω′(z_N)⟩ + ω(z_N)] ≤ ω(u)`;
(4) the resulting bound; (5) its last step, the bound by `Θ(z₀)`; and (6) the end-to-end
inequality.

Standing assumptions as in (2.15): `Z` convex compact, `N` a norm, (2.1), (2.2), and `n`
non-terminating steps of the relaxed CPM.

**Formalization Note.** `n : ℕ` includes `n = 0`, where both sums are empty and the claims
are the trivially true empty-sum instances. -/
theorem eq_2_16_summed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Z : Set E} (hZc : Convex ℝ Z) (hZk : IsCompact Z)
    {N : Seminorm ℝ E} (hN : ∀ x, N x = 0 → x = 0)
    {α : ℝ} {ω : E → ℝ} {ω' : E → E} (hω : IsDistGen Z N α ω ω')
    {L : ℝ} {F : E → E} (hF : IsLipMonotoneOn Z N L F)
    {γs εs : ℕ → ℝ} {z w : ℕ → E} {n : ℕ} (hrun : IsRelaxedCPMRun Z F ω ω' γs εs z w n) :
    ∀ u ∈ Z,
      (∑ t ∈ Finset.Icc 1 n, γs t * ⟪F (w t), w t - u⟫_ℝ ≤
          Hfun Z ω ω' u (z 0) - Hfun Z ω ω' u (z n) + ∑ t ∈ Finset.Icc 1 n, εs t) ∧
        (Hfun Z ω ω' u (z 0) - Hfun Z ω ω' u (z n) =
          (⟪z 0 - u, ω' (z 0)⟫_ℝ - ω (z 0)) + (⟪u - z n, ω' (z n)⟫_ℝ + ω (z n))) ∧
        (⟪u - z n, ω' (z n)⟫_ℝ + ω (z n) ≤ ω u) ∧
        (∑ t ∈ Finset.Icc 1 n, γs t * ⟪F (w t), w t - u⟫_ℝ ≤
          ω u - ⟪ω' (z 0), u - z 0⟫_ℝ - ω (z 0) + ∑ t ∈ Finset.Icc 1 n, εs t) ∧
        (ω u - ⟪ω' (z 0), u - z 0⟫_ℝ - ω (z 0) + ∑ t ∈ Finset.Icc 1 n, εs t ≤
          Theta Z ω ω' (z 0) + ∑ t ∈ Finset.Icc 1 n, εs t) ∧
        (∑ t ∈ Finset.Icc 1 n, γs t * ⟪F (w t), w t - u⟫_ℝ ≤
          Theta Z ω ω' (z 0) + ∑ t ∈ Finset.Icc 1 n, εs t) := by sorry

end NemirovskiProx
