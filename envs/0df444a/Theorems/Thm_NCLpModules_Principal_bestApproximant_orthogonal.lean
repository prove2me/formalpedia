-- Prove2me | Theorems.Thm_NCLpModules_Principal_bestApproximant_orthogonal
-- name    : NCLpModules.Principal.bestApproximant_orthogonal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:10.281022+00:00
-- url     : https://prove2.me/theorems/8e87ead8-61e4-4b2e-939c-18439923a7d3
-- title:
--   Proof of Theorem 2.5, Case 2 (p > 2), pp. 12–13 — if 0 is a best approximant of ζ from 𝔛_0, then ⟨ζ, ξ_λ⟩ = 0 for every λ
-- statement:
--   Let $\mathcal M\subseteq M_n(\mathbb C)$ be a unital $*$-subalgebra, $2<p<\infty$, and $\mathfrak X$ a right $L^p$ $\mathcal M$-module with norm $\|\xi\|=\|\langle\xi,\xi\rangle^{1/2}\|_p$. Let $(\xi_\lambda)_{\lambda\in I}$ be an orthogonal family ($\langle\xi_\alpha,\xi_\beta\rangle=0$ for $\alpha\ne\beta$) and $\mathfrak X_0=\overline{\sum_\lambda\xi_\lambda\mathcal M}$ its closed span. If $\zeta\in\mathfrak X$ has $0$ as a best approximant from $\mathfrak X_0$,
--   $$\|\zeta\|\le\|\zeta-\eta\|\quad\text{for all }\eta\in\mathfrak X_0,$$
--   then
--   $$\langle\zeta,\xi_\lambda\rangle=0\quad\text{for every }\lambda\in I.$$
--
--   In the proof of Theorem 2.5 (Case 2) this shows that the residue $\zeta=\xi-\eta_0$ of a best approximation would enlarge a maximal orthogonal family, so $\mathfrak X_0=\mathfrak X$.
--
--   **Formalization Note** Finite-dimensional scope. The page's index switches from $\alpha$ to $\lambda$ after "Fix $\alpha$ and $x\in\mathcal M$"; the conclusion is for every index. The page's display on p. 13 writes $\|\zeta+t\xi_\lambda x\|$ where $\|\zeta+t\xi_\lambda x\|^2$ is meant; this concerns the proof only. The assumptions $\zeta\notin\mathfrak X_0$ and $\zeta\ne0$ of the page are not needed for the conclusion and are not imposed (for $\zeta=0$ it is trivial), and maximality of the family is not assumed. $p>2$ is Case 2's standing assumption.
-- source:
--   Junge & Sherman, Noncommutative Lp modules, arXiv:math/0301044v2, pp. 12–13, proof of Theorem 2.5, Case 2: 'Then ζ = ξ − η_0 has 0 as a best approximant' through 'Together (3.2) and (3.3) imply ⟨ζ, ξ_λ⟩ = … = 0'

import Mathlib
import Definitions.Def_NCLpModules_Principal_Model

namespace NCLpModules.Principal

open scoped Matrix ComplexOrder

theorem bestApproximant_orthogonal {n : ℕ} (M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    {p : ℝ} (hp : 2 < p)
    {𝔛 : Type*} [AddCommGroup 𝔛] [Module ℂ 𝔛]
    (act : 𝔛 → Matrix (Fin n) (Fin n) ℂ → 𝔛) (ip : LpInnerProduct M 𝔛 act)
    (hX : IsLpModule p M act ip)
    {ι : Type*} (ξ : ι → 𝔛) (horth : ∀ α β, α ≠ β → ip.ip (ξ α) (ξ β) = 0)
    (ζ : 𝔛) (hbest : ∀ η ∈ gaugeClosure p ip (spanSet M act ξ), gauge p ip ζ ≤ gauge p ip (ζ - η)) :
    ∀ l : ι, ip.ip ζ (ξ l) = 0 := by sorry

end NCLpModules.Principal
