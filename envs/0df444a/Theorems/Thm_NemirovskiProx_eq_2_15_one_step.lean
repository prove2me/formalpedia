-- Prove2me | Theorems.Thm_NemirovskiProx_eq_2_15_one_step
-- name    : NemirovskiProx.eq_2_15_one_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:49:11.290716+00:00
-- url     : https://prove2.me/theorems/e8e38aac-66d9-45cc-a8be-50125f00a0bc
-- title:
--   (2.15): one step of the relaxed conceptual prox-method
-- statement:
--   Assume the standing assumptions of §2.1–2.2: $Z$ is a convex compact set in a Euclidean space $E$, $\|\cdot\|$ a norm on $E$, $F$ satisfies (2.1), and $\omega$ satisfies (2.2). Let $z_0,w_1,z_1,\dots$ be a run of the relaxed conceptual prox-method with stepsizes $\gamma_t>0$ and tolerances $\epsilon_t$ in (2.11) that does not terminate in the course of $N$ steps. Then for every $t\le N$ and every $u\in Z$,
--   $$\langle\gamma_tF(w_t),w_t-u\rangle\le H_u(z_{t-1})-H_u(z_t)+\epsilon_t. \tag{2.15}$$
--
--   It is obtained in the proof of Proposition 2.2 from (2.5) and (2.11), and summed over $t$ it gives (2.16).
--
--   Differences from the source:
--   - encoding: ‖·‖ is a norm on E and ‖ξ‖∗ = max_{z:‖z‖≤1}⟨ξ, z⟩ → a seminorm N on E with N x = 0 → x = 0, and ‖ξ‖∗ = sSup of ⟨ξ, z⟩ over N z ≤ 1; reason: a definite seminorm is a norm; Lean's ‖·‖ on E is the inner-product norm, so the paper's norm is a separate object; the supremum is attained on the compact unit ball of finite-dimensional E
--   - encoding: ω : Z → R continuously differentiable with derivative ω′, F : Z → E → ω, ω′, F are functions on all of E; ω′(z) is a gradient of ω at z within Z and ω′ is continuous on Z; reason: only the values on Z enter any statement; the paper's ω′ is such a gradient field and no interior point of Z is assumed
--   - encoding: argmin and max/min over compact sets → a predicate for the minimizer (IsProxPointOn) and sSup/sInf of images; reason: the minimizer exists and is unique by compactness and strong convexity, and every supremum/infimum is over a nonempty compact image of a continuous function, hence attained
--   - encoding: the relaxed CPM (p. 233, with (2.11) for (2.9)) not terminating in the course of N steps; step t = 1, …, N → IsRelaxedCPMRun: z 0 ∈ Z and for each t < n, z t fails (2.8), γs (t+1) > 0, w (t+1) ∈ Z, z (t+1) is the prox point of γs (t+1) F(w (t+1)) at z t, and (2.11) holds; reason: the paper's step t is t + 1 here, avoiding natural subtraction; same runs
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, proof of Proposition 2.2, eq. (2.15), p. 235

import Mathlib
import Definitions.Def_NemirovskiProx_dualNorm
import Definitions.Def_NemirovskiProx_IsLipMonotoneOn
import Definitions.Def_NemirovskiProx_IsDistGen
import Definitions.Def_NemirovskiProx_IsProxPointOn
import Definitions.Def_NemirovskiProx_stepGap
import Definitions.Def_NemirovskiProx_IsRelaxedCPMRun
import Definitions.Def_NemirovskiProx_legendre
import Definitions.Def_NemirovskiProx_Hfun

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **(2.15): one step of the relaxed conceptual prox-method.**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), proof of Proposition 2.2, (2.15), p. 235: "⟨γtF(wt), wt − u⟩ ≤ Hu(zt−1) − Hu(zt) + ϵt."
(for every u ∈ Z and every t ≤ N).

Standing assumptions (§2.1–2.2, p. 232): `Z` convex compact, `N` a norm, `F` satisfies (2.1)
with constant `L`, `ω` satisfies (2.2). The run is `n` non-terminating steps of the relaxed CPM
(Proposition 2.2, p. 234), with stepsizes `γs t > 0` and tolerances `εs t` in (2.11).

**Formalization Note.** The paper's step `t` is `t + 1` here, for `t < n`; `z 0` is `z₀`. -/
theorem eq_2_15_one_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Z : Set E} (hZc : Convex ℝ Z) (hZk : IsCompact Z)
    {N : Seminorm ℝ E} (hN : ∀ x, N x = 0 → x = 0)
    {α : ℝ} {ω : E → ℝ} {ω' : E → E} (hω : IsDistGen Z N α ω ω')
    {L : ℝ} {F : E → E} (hF : IsLipMonotoneOn Z N L F)
    {γs εs : ℕ → ℝ} {z w : ℕ → E} {n : ℕ} (hrun : IsRelaxedCPMRun Z F ω ω' γs εs z w n) :
    ∀ t < n, ∀ u ∈ Z,
      ⟪γs (t + 1) • F (w (t + 1)), w (t + 1) - u⟫_ℝ ≤
        Hfun Z ω ω' u (z t) - Hfun Z ω ω' u (z (t + 1)) + εs (t + 1) := by sorry

end NemirovskiProx
