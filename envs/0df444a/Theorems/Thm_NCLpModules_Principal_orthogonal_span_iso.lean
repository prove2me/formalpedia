-- Prove2me | Theorems.Thm_NCLpModules_Principal_orthogonal_span_iso
-- name    : NCLpModules.Principal.orthogonal_span_iso
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:16.631864+00:00
-- url     : https://prove2.me/theorems/b2167f5e-df3c-4e78-af52-894b9a503bad
-- title:
--   Proof of Theorem 2.5, Case 2 (p > 2), p. 12 — the closed span 𝔛_0 of an orthogonal family {ξ_α} is isomorphic to ⊕_c q_α L^p
-- statement:
--   Let $\mathcal M\subseteq M_n(\mathbb C)$ be a unital $*$-subalgebra, $2<p<\infty$, and $\mathfrak X$ a right $L^p$ $\mathcal M$-module. Let $(\xi_\alpha)_{\alpha\in I}$ be an orthogonal family, $\langle\xi_\alpha,\xi_\beta\rangle=0$ for $\alpha\neq\beta$ (no condition on $\langle\xi_\alpha,\xi_\alpha\rangle$), let
--   $$\mathfrak X_0=\overline{\textstyle\sum_\alpha\xi_\alpha\mathcal M}$$
--   be the closure in $\|\cdot\|$ of the finite sums $\sum_{\alpha\in F}\xi_\alpha x_\alpha$ ($x_\alpha\in\mathcal M$), and let $q_\alpha=s(\langle\xi_\alpha,\xi_\alpha\rangle)$. Then there is an isomorphism of $L^p$ modules
--   $$\mathfrak X_0\ni\eta\ \longleftrightarrow\ \textstyle\bigoplus_c q_\alpha L^p ,$$
--   i.e. a map $T$ sending $\mathfrak X_0$ bijectively onto the column sum (2.4), complex linear and right $\mathcal M$-linear on $\mathfrak X_0$, with $\langle T\eta,T\eta'\rangle=\langle\eta,\eta'\rangle$ for $\eta,\eta'\in\mathfrak X_0$.
--
--   It is the first half of Case 2 of the proof of Theorem 2.5: once $\mathfrak X_0=\mathfrak X$ for a maximal family, $\mathfrak X$ is principal.
--
--   **Formalization Note** Finite-dimensional scope; the closure is kept ($\mathfrak X_0$ need not be finite-dimensional). Two printed slips are read as meant: "$\sum\xi\mathcal M$" is $\sum_\alpha\xi_\alpha\mathcal M$, and $q_\alpha$, undefined in Case 2, is the support projection $s(\langle\xi_\alpha,\xi_\alpha\rangle)$ $(=s(\langle\xi_\alpha,\xi_\alpha\rangle^{1/2}))$ as in the cyclic case. The page assumes the family is a *maximal* orthogonal set; this step does not use maximality, so it is stated for any orthogonal family (a disclosed generalization of the hypothesis). $p>2$ is kept from Case 2. The isomorphism preserves the column inner product $\sum_\alpha(T\eta)_\alpha^*(T\eta')_\alpha$, hence the norm.
-- source:
--   Junge & Sherman, Noncommutative Lp modules, arXiv:math/0301044v2, p. 12, proof of Theorem 2.5, Case 2: 𝔛_0 = closure(Σ ξM) ≃ ⊕_c q_α L^p and 'we have an isomorphism of L^p modules 𝔛_0 ∋ η ↔ ⊕_c q_α L^p'

import Mathlib
import Definitions.Def_NCLpModules_Principal_Model

namespace NCLpModules.Principal

open scoped Matrix ComplexOrder

theorem orthogonal_span_iso {n : ℕ} (M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    {p : ℝ} (hp : 2 < p)
    {𝔛 : Type*} [AddCommGroup 𝔛] [Module ℂ 𝔛]
    (act : 𝔛 → Matrix (Fin n) (Fin n) ℂ → 𝔛) (ip : LpInnerProduct M 𝔛 act)
    (hX : IsLpModule p M act ip)
    {ι : Type*} (ξ : ι → 𝔛) (horth : ∀ α β, α ≠ β → ip.ip (ξ α) (ξ β) = 0) :
    ∃ T : 𝔛 → ι → Matrix (Fin n) (Fin n) ℂ,
      (∀ η ∈ gaugeClosure p ip (spanSet M act ξ),
        T η ∈ columnSumSet M (fun α => supportProj (ip.ip (ξ α) (ξ α)))) ∧
      Set.InjOn T (gaugeClosure p ip (spanSet M act ξ)) ∧
      (∀ z ∈ columnSumSet M (fun α => supportProj (ip.ip (ξ α) (ξ α))),
        ∃ η ∈ gaugeClosure p ip (spanSet M act ξ), T η = z) ∧
      (∀ (c : ℂ), ∀ η ∈ gaugeClosure p ip (spanSet M act ξ),
        ∀ η' ∈ gaugeClosure p ip (spanSet M act ξ), T (c • η + η') = c • T η + T η') ∧
      (∀ η ∈ gaugeClosure p ip (spanSet M act ξ), ∀ x ∈ M,
        T (act η x) = fun α => T η α * x) ∧
      (∀ η ∈ gaugeClosure p ip (spanSet M act ξ), ∀ η' ∈ gaugeClosure p ip (spanSet M act ξ),
        colIp (T η) (T η') = ip.ip η η') := by sorry

end NCLpModules.Principal
