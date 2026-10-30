-- Prove2me | Theorems.Thm_NemirovskiProx_lemma_3_1
-- name    : NemirovskiProx.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:34:57.476262+00:00
-- url     : https://prove2.me/theorems/3365893e-93b5-4ff4-958a-cdccf35c331a
-- title:
--   Lemma 3.1: two-point prox inequalities (3.7)
-- statement:
--   Let $Z$, $\|\cdot\|$ and $\omega$ satisfy the standing assumptions of §2.1–2.2 ($Z$ convex compact in a Euclidean space $E$, $\omega$ continuously differentiable and $\alpha$-strongly convex on $Z$). Let a nonempty set $U\subset Z$ be convex and closed, let $z\in Z$, let $\xi,\eta\in E$, and let $\gamma>0$. Consider the points
--   $$w=\operatorname*{argmin}_{y\in U}\big[\langle\gamma\xi-\omega'(z),y\rangle+\omega(y)\big],\qquad z_+=\operatorname*{argmin}_{y\in U}\big[\langle\gamma\eta-\omega'(z),y\rangle+\omega(y)\big]. \tag{3.6}$$
--   Put
--   $$\delta=\langle\gamma\eta,w-z_+\rangle+\big[\omega(z)+\langle\omega'(z),z_+-z\rangle-\omega(z_+)\big],$$
--   $$\epsilon=\langle\gamma(\eta-\xi),w-z_+\rangle+\big[\omega(z)+\langle\omega'(z),w-z\rangle+\langle\omega'(w),z_+-w\rangle-\omega(z_+)\big].$$
--   Then
--
--   1. $\|w-z_+\|\le\alpha^{-1}\gamma\|\xi-\eta\|_*$;
--   2. $\langle\gamma\eta,w-u\rangle\le H_u(z)-H_u(z_+)+\delta$ for all $u\in U$;
--   3. $\delta\le\epsilon$;
--   4. $\epsilon\le\alpha^{-1}\gamma^2\|\xi-\eta\|_*^2-\frac{\alpha}{2}\big[\|w-z\|^2+\|w-z_+\|^2\big]$. (3.7)
--
--   With $U=Z$, $\xi=F(z)$, $\eta=F(w)$ this is the estimate that makes the stopping test (3.4) hold at the second inner iteration in Theorem 3.2.
--
--   Differences from the source:
--   - encoding: ‖·‖ is a norm on E and ‖ξ‖∗ = max_{z:‖z‖≤1}⟨ξ, z⟩ → a seminorm N on E with N x = 0 → x = 0, and ‖ξ‖∗ = sSup of ⟨ξ, z⟩ over N z ≤ 1; reason: a definite seminorm is a norm; Lean's ‖·‖ on E is the inner-product norm, so the paper's norm is a separate object; the supremum is attained on the compact unit ball of finite-dimensional E
--   - encoding: ω : Z → R continuously differentiable with derivative ω′ → ω, ω′ are functions on all of E; ω′(z) is a gradient of ω at z within Z and ω′ is continuous on Z; reason: only the values on Z enter the statement; the paper's ω′ is such a gradient field and no interior point of Z is assumed
--   - encoding: argmin and max/min over compact sets → a predicate for the minimizer (IsProxPointOn) and sSup/sInf of images; reason: the minimizer exists and is unique by compactness and strong convexity, and every supremum/infimum is over a nonempty compact image of a continuous function, hence attained
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, Lemma 3.1, (3.6)–(3.7), pp. 237–238

import Mathlib
import Definitions.Def_NemirovskiProx_dualNorm
import Definitions.Def_NemirovskiProx_IsDistGen
import Definitions.Def_NemirovskiProx_IsProxPointOn
import Definitions.Def_NemirovskiProx_legendre
import Definitions.Def_NemirovskiProx_Hfun

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **Lemma 3.1: the two-point prox inequalities (3.7.a)–(3.7.d).**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), Lemma 3.1, (3.6)–(3.7), pp. 237–238: "Let a nonempty set U ⊂ Z be convex and closed,
and let z ∈ Z. Let ξ, η be two points from E, and let γ > 0. Consider the points
w = argmin_{y∈U} [⟨γξ − ω′(z), y⟩ + ω(y)], z+ = argmin_{y∈U} [⟨γη − ω′(z), y⟩ + ω(y)]. (3.6)
Then for all u ∈ U one has (a) ‖w − z+‖ ≤ α^{−1}γ‖ξ − η‖∗, (b) ⟨γη, w − u⟩ ≤ Hu(z) − Hu(z+) + δ,
(c) δ ≤ ϵ, (d) ϵ ≤ α^{−1}γ²‖ξ − η‖²∗ − (α/2)[‖w − z‖² + ‖w − z+‖²]", where (underbraces on
p. 238) δ = ⟨γη, w − z+⟩ + [ω(z) + ⟨ω′(z), z+ − z⟩ − ω(z+)] and ϵ = ⟨γ(η − ξ), w − z+⟩ +
[ω(z) + ⟨ω′(z), w − z⟩ + ⟨ω′(w), z+ − w⟩ − ω(z+)].

Standing assumptions (§2.1–2.2, p. 232): `Z` convex compact, `N` a norm, `ω` satisfies (2.2).

**Formalization Note.** `w`, `z+` are given by the argmin predicate `IsProxPointOn U` (with
`γ • ξ`, `γ • η`); `H_u` is the function (2.3), built from the Legendre transformation over
`Z`, as on p. 232. δ and ϵ are written out. -/
theorem lemma_3_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Z : Set E} (hZc : Convex ℝ Z) (hZk : IsCompact Z)
    {N : Seminorm ℝ E} (hN : ∀ x, N x = 0 → x = 0)
    {α : ℝ} {ω : E → ℝ} {ω' : E → E} (hω : IsDistGen Z N α ω ω')
    {U : Set E} (hU : U.Nonempty) (hUc : Convex ℝ U) (hUcl : IsClosed U) (hUZ : U ⊆ Z)
    {z : E} (hz : z ∈ Z) (ξ η : E) {γ : ℝ} (hγ : 0 < γ) {w zp : E}
    (hw : IsProxPointOn U ω ω' z (γ • ξ) w) (hzp : IsProxPointOn U ω ω' z (γ • η) zp) :
    N (w - zp) ≤ α⁻¹ * γ * dualNorm N (ξ - η) ∧
      (∀ u ∈ U, ⟪γ • η, w - u⟫_ℝ ≤ Hfun Z ω ω' u z - Hfun Z ω ω' u zp +
          (⟪γ • η, w - zp⟫_ℝ + (ω z + ⟪ω' z, zp - z⟫_ℝ - ω zp))) ∧
      ⟪γ • η, w - zp⟫_ℝ + (ω z + ⟪ω' z, zp - z⟫_ℝ - ω zp) ≤
        ⟪γ • (η - ξ), w - zp⟫_ℝ + (ω z + ⟪ω' z, w - z⟫_ℝ + ⟪ω' w, zp - w⟫_ℝ - ω zp) ∧
      ⟪γ • (η - ξ), w - zp⟫_ℝ + (ω z + ⟪ω' z, w - z⟫_ℝ + ⟪ω' w, zp - w⟫_ℝ - ω zp) ≤
        α⁻¹ * γ ^ 2 * dualNorm N (ξ - η) ^ 2 - α / 2 * (N (w - z) ^ 2 + N (w - zp) ^ 2) := by sorry

end NemirovskiProx
