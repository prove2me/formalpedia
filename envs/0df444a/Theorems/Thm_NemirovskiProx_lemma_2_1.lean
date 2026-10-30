-- Prove2me | Theorems.Thm_NemirovskiProx_lemma_2_1
-- name    : NemirovskiProx.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:48:29.184602+00:00
-- url     : https://prove2.me/theorems/468a7563-e141-4f9a-a46c-342015bf044a
-- title:
--   Lemma 2.1: the prox-mapping is $\alpha^{-1}$-Lipschitz, and (2.5)
-- statement:
--   Let $Z$ be a convex compact set in a Euclidean space $E$, $\|\cdot\|$ a norm on $E$ with dual norm $\|\cdot\|_*$, and $\omega$ a continuously differentiable function on $Z$ that is strongly convex with modulus $\alpha>0$ (2.2). Fix $z\in Z$ and let $P_z(\xi)=\operatorname{argmin}_{w\in Z}[\omega(w)+\langle w,\xi-\omega'(z)\rangle]$. Then:
--
--   1. $P_z$ is Lipschitz continuous:
--   $$\|P_z(\xi)-P_z(\eta)\|\le\alpha^{-1}\|\xi-\eta\|_*\qquad\forall\xi,\eta\in E; \tag{2.4}$$
--   2. for every $\xi\in E$ and every $u\in Z$,
--   $$H_u(P_z(\xi))-H_u(z)\le\langle\xi,u-P_z(\xi)\rangle+\big[\omega(z)+\langle\omega'(z),P_z(\xi)-z\rangle-\omega(P_z(\xi))\big], \tag{2.5}$$
--   and the bracket is $\le0$.
--
--   Here $H_u$ is the function (2.3). The lemma is the one-step estimate behind (2.15) and hence behind every error bound of the paper.
--
--   Differences from the source:
--   - encoding: ‖·‖ is a norm on E and ‖ξ‖∗ = max_{z:‖z‖≤1}⟨ξ, z⟩ → a seminorm N on E with N x = 0 → x = 0, and ‖ξ‖∗ = sSup of ⟨ξ, z⟩ over N z ≤ 1; reason: a definite seminorm is a norm; Lean's ‖·‖ on E is the inner-product norm, so the paper's norm is a separate object; the supremum is attained on the compact unit ball of finite-dimensional E
--   - encoding: ω : Z → R continuously differentiable with derivative ω′ → ω, ω′ are functions on all of E; ω′(z) is a gradient of ω at z within Z and ω′ is continuous on Z; reason: only the values on Z enter the statement; the paper's ω′ is such a gradient field and no interior point of Z is assumed
--   - encoding: argmin and max/min over compact sets → a predicate for the minimizer (IsProxPointOn) and sSup/sInf of images; reason: the minimizer exists and is unique by compactness and strong convexity, and every supremum/infimum is over a nonempty compact image of a continuous function, hence attained
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, Lemma 2.1, (2.4)–(2.5), p. 232

import Mathlib
import Definitions.Def_NemirovskiProx_dualNorm
import Definitions.Def_NemirovskiProx_IsDistGen
import Definitions.Def_NemirovskiProx_IsProxPointOn
import Definitions.Def_NemirovskiProx_legendre
import Definitions.Def_NemirovskiProx_Hfun

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **Lemma 2.1: the prox-mapping is `α⁻¹`-Lipschitz, and inequality (2.5).**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), Lemma 2.1, (2.4)–(2.5), p. 232: "The mapping Pz is Lipschitz continuous; specifically,
‖Pz(ξ) − Pz(η)‖ ≤ α^{−1}‖ξ − η‖∗ ∀ξ, η ∈ E. (2.4) Besides this, ∀(u ∈ Z): Hu(Pz(ξ)) − Hu(z) ≤
⟨ξ, u − Pz(ξ)⟩ + [ω(z) + ⟨ω′(z), Pz(ξ) − z⟩ − ω(Pz(ξ))] (the bracket ≤ 0). (2.5)"

Standing assumptions (§2.1–2.2, p. 232): `Z` convex compact, `N` a norm, `ω` continuously
differentiable and `α`-strongly convex on `Z` (2.2); `z ∈ Z`.

**Formalization Note.** `Pz(ξ)` is any `p` with `IsProxPointOn Z ω ω' z ξ p` (it exists and is
unique). The underbrace "≤ 0" under the bracket of (2.5) is stated as its own clause. The
paper's ‖·‖ is the seminorm `N` with definiteness `hN`, ‖·‖∗ is `dualNorm N`. -/
theorem lemma_2_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Z : Set E} (hZc : Convex ℝ Z) (hZk : IsCompact Z)
    {N : Seminorm ℝ E} (hN : ∀ x, N x = 0 → x = 0)
    {α : ℝ} {ω : E → ℝ} {ω' : E → E} (hω : IsDistGen Z N α ω ω') {z : E} (hz : z ∈ Z) :
    (∀ ξ η p q : E, IsProxPointOn Z ω ω' z ξ p → IsProxPointOn Z ω ω' z η q →
        N (p - q) ≤ α⁻¹ * dualNorm N (ξ - η)) ∧
      (∀ ξ p : E, IsProxPointOn Z ω ω' z ξ p →
        (∀ u ∈ Z, Hfun Z ω ω' u p - Hfun Z ω ω' u z ≤
            ⟪ξ, u - p⟫_ℝ + (ω z + ⟪ω' z, p - z⟫_ℝ - ω p)) ∧
          ω z + ⟪ω' z, p - z⟫_ℝ - ω p ≤ 0) := by sorry

end NemirovskiProx
