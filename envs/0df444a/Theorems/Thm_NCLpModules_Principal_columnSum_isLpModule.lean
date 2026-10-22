-- Prove2me | Theorems.Thm_NCLpModules_Principal_columnSum_isLpModule
-- name    : NCLpModules.Principal.columnSum_isLpModule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:09.67049+00:00
-- url     : https://prove2.me/theorems/14f13cbd-d500-4ed4-b809-c236518ea685
-- title:
--   Display (2.4), p. 10 — the column sum ⊕_c q_α L^p is a right L^p M-module, with ‖⟨(ξ_α),(η_α)⟩‖_{p/2} ≤ ‖ξ‖‖η‖
-- statement:
--   Let $\mathcal M\subseteq M_n(\mathbb C)$ be a unital $*$-subalgebra, $0<p<\infty$, $I$ any index set and $(q_\alpha)_{\alpha\in I}$ projections of $\mathcal M$. Let $X=\bigoplus_c q_\alpha L^p$ be the set (2.4) of families $(\xi_\alpha)$ with $\xi_\alpha\in q_\alpha L^p$ and $\sum_\alpha\xi_\alpha^*\xi_\alpha$ convergent, with $\langle(\xi_\alpha),(\eta_\alpha)\rangle=\sum_\alpha\xi_\alpha^*\eta_\alpha$ and $\|\xi\|=\|\langle\xi,\xi\rangle^{1/2}\|_p$. Then:
--
--   1. $X$ contains $0$ and is closed under addition, complex scalars, and the right action $(\xi_\alpha)x=(\xi_\alpha x)$, $x\in\mathcal M$;
--   2. for $\xi,\eta\in X$ the series $\sum_\alpha\xi_\alpha^*\eta_\alpha$ converges, and
--   $$\|\langle(\xi_\alpha),(\eta_\alpha)\rangle\|_{p/2}\le\|\xi\|\,\|\eta\|;$$
--   3. $\langle\cdot,\cdot\rangle$ takes values in $\mathcal M$ and satisfies Definition 2.1 on $X$: sesquilinear (conjugate linear in the first variable), $\langle\xi,\eta x\rangle=\langle\xi,\eta\rangle x$, $\langle\xi,\eta\rangle=\langle\eta,\xi\rangle^*$, $\langle\xi,\xi\rangle\ge0$ and $\langle\xi,\xi\rangle=0\iff\xi=0$;
--   4. $X$ is complete: every $\|\cdot\|$-Cauchy sequence in $X$ converges in $\|\cdot\|$ to an element of $X$.
--
--   Hence $\bigoplus_c q_\alpha L^p$ is a right $L^p$ $\mathcal M$-module (Definition 2.3), the "principal" modules onto which Theorem 2.5 maps every $L^p$ module.
--
--   **Formalization Note** Finite-dimensional scope. Because the column sum is defined as a set of families $I\to M_n(\mathbb C)$ (a type with module structure would need these very facts to be built), the statement "is a right $L^p$ $\mathcal M$-module" is unpacked into clauses 1–4. Convergence of $\sum_\alpha$ is unconditional summability (the net of finite sums converges, as on p. 10); clause 2 asserts summability of $(\xi_\alpha^*\eta_\alpha)$ before its sum is used, so no default value of `tsum` is involved. The index type is arbitrary.
-- source:
--   Junge & Sherman, Noncommutative Lp modules, arXiv:math/0301044v2, p. 10, display (2.4), the sentence 'For p < ∞, the limit (of finite sums) exists in norm' and the Cauchy–Schwarz display

import Mathlib
import Definitions.Def_NCLpModules_Principal_Model

namespace NCLpModules.Principal

open scoped Matrix ComplexOrder

open Filter
open scoped Topology

theorem columnSum_isLpModule {n : ℕ} (M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    {p : ℝ} (hp : 0 < p) {ι : Type*}
    (q : ι → Matrix (Fin n) (Fin n) ℂ) (hq : ∀ α, IsProj M (q α)) :
    -- (a) a right M-submodule of the families ι → M_n(ℂ)
    (0 : ι → Matrix (Fin n) (Fin n) ℂ) ∈ columnSumSet M q ∧
    (∀ ξ ∈ columnSumSet M q, ∀ η ∈ columnSumSet M q, ξ + η ∈ columnSumSet M q) ∧
    (∀ (c : ℂ), ∀ ξ ∈ columnSumSet M q, c • ξ ∈ columnSumSet M q) ∧
    (∀ ξ ∈ columnSumSet M q, ∀ x ∈ M, (fun α => ξ α * x) ∈ columnSumSet M q) ∧
    -- (b) the sum converges, with the Cauchy–Schwarz bound
    (∀ ξ ∈ columnSumSet M q, ∀ η ∈ columnSumSet M q,
      Summable (fun α => (ξ α)ᴴ * η α) ∧
      lpNorm (p / 2) (colIp ξ η) ≤ ipNorm p (colIp ξ ξ) * ipNorm p (colIp η η)) ∧
    -- (c) Definition 2.1 (i)–(iii) for colIp, with values in M
    (∀ ξ ∈ columnSumSet M q, ∀ η ∈ columnSumSet M q, colIp ξ η ∈ M) ∧
    (∀ ξ ∈ columnSumSet M q, ∀ ξ' ∈ columnSumSet M q, ∀ η ∈ columnSumSet M q, ∀ c : ℂ,
      colIp (c • ξ + ξ') η = star c • colIp ξ η + colIp ξ' η ∧
      colIp η (c • ξ + ξ') = c • colIp η ξ + colIp η ξ') ∧
    (∀ ξ ∈ columnSumSet M q, ∀ η ∈ columnSumSet M q, ∀ x ∈ M,
      colIp ξ (fun α => η α * x) = colIp ξ η * x) ∧
    (∀ ξ ∈ columnSumSet M q, ∀ η ∈ columnSumSet M q, colIp ξ η = (colIp η ξ)ᴴ) ∧
    (∀ ξ ∈ columnSumSet M q, (colIp ξ ξ).PosSemidef ∧ (colIp ξ ξ = 0 ↔ ξ = 0)) ∧
    -- (d) completeness in the norm ‖ξ‖ = ‖⟨ξ, ξ⟩^{1/2}‖_p
    (∀ u : ℕ → ι → Matrix (Fin n) (Fin n) ℂ, (∀ k, u k ∈ columnSumSet M q) →
      (∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ k ≥ N, ipNorm p (colIp (u m - u k) (u m - u k)) < ε) →
      ∃ x ∈ columnSumSet M q,
        Tendsto (fun k => ipNorm p (colIp (u k - x) (u k - x))) atTop (𝓝 0)) := by sorry

end NCLpModules.Principal
