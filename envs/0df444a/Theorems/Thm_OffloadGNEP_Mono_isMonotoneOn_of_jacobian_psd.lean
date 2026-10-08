-- Prove2me | Theorems.Thm_OffloadGNEP_Mono_isMonotoneOn_of_jacobian_psd
-- name    : OffloadGNEP.Mono.isMonotoneOn_of_jacobian_psd
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:37.05619+00:00
-- url     : https://prove2.me/theorems/e0a91caf-7696-477f-9668-49b31831b26f
-- title:
--   p. 12 — a map whose Jacobian is positive semidefinite on a convex set is monotone there
-- statement:
--   Let $S\subseteq\mathbb R^{3N}$ be convex and let $G:\mathbb R^{3N}\to\mathbb R^{3N}$ be Fréchet differentiable at every point of $S$, with derivative $G'(x)$ at $x$. If the derivative is positive semidefinite on $S$ in the sense that
--   $$h^\top G'(x)\,h\ \ge\ 0\qquad\text{for all }x\in S,\ h\in\mathbb R^{3N},$$
--   then $G$ is monotone on $S$: $(G(y)-G(x))^\top(y-x)\ge0$ for all $x,y\in S$.
--
--   This is the criterion the paper invokes (citing Facchinei–Pang) to reduce the monotonicity of the VI map $F$ to a property of its Jacobian $JF$.
--
--   **Formalization Note** Differentiability is required at the points of $S$ only (as `HasFDerivAt`, i.e. in a full neighbourhood in $\mathbb R^{3N}$), which is how the criterion is applied: the paper's $F$ is differentiable on an open set containing $K$, while $K$ itself has empty interior. The inner product is the Euclidean one, summed over all $3N$ coordinates.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), p. 12, paragraph before (16) (citing [17])

import Mathlib
import Definitions.Def_OffloadGNEP_Mono_Setting

namespace OffloadGNEP.Mono

theorem isMonotoneOn_of_jacobian_psd {N : ℕ} (S : Set (Fin N → Tier → ℝ))
    (G : (Fin N → Tier → ℝ) → (Fin N → Tier → ℝ))
    (G' : (Fin N → Tier → ℝ) → ((Fin N → Tier → ℝ) →L[ℝ] (Fin N → Tier → ℝ)))
    (hS : Convex ℝ S) (hG : ∀ x ∈ S, HasFDerivAt G (G' x) x)
    (hpsd : ∀ x ∈ S, ∀ h : Fin N → Tier → ℝ, 0 ≤ pair h (G' x h)) :
    IsMonotoneOn S G := by sorry

end OffloadGNEP.Mono
