-- Prove2me | Theorems.Thm_NCLpModules_Principal_theorem_2_5
-- name    : NCLpModules.Principal.theorem_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:26.424143+00:00
-- url     : https://prove2.me/theorems/335211f9-b537-49f2-8c72-aeb0e348dc02
-- title:
--   Theorem 2.5, p. 10 — every L^p module over a finite-dimensional von Neumann algebra is isometrically isomorphic, as a module, to a principal column sum ⊕_c q_α L^p
-- statement:
--   Let $\mathcal M\subseteq M_n(\mathbb C)$ be a unital $*$-subalgebra (a finite-dimensional von Neumann algebra), $0<p<\infty$, and let $\mathfrak X$ be a right $L^p$ $\mathcal M$-module: a complex vector space with a right $\mathcal M$-action and an $L^{p/2}$-valued inner product $\langle\cdot,\cdot\rangle$ (Definition 2.1), complete in $\|\xi\|=\|\langle\xi,\xi\rangle^{1/2}\|_p$ (Definition 2.3). Then there are an index set $I$, projections $(q_\alpha)_{\alpha\in I}$ of $\mathcal M$ and a map
--   $$T:\mathfrak X\longrightarrow\textstyle\bigoplus_c q_\alpha L^p$$
--   onto the column sum (2.4) which is
--
--   1. bijective onto $\bigoplus_c q_\alpha L^p$;
--   2. complex linear;
--   3. a module map: $T(\xi x)=(T(\xi)_\alpha\,x)_\alpha$ for $x\in\mathcal M$;
--   4. isometric: $\big\|\big(\sum_\alpha T(\xi)_\alpha^*T(\xi)_\alpha\big)^{1/2}\big\|_p=\|\langle\xi,\xi\rangle^{1/2}\|_p$.
--
--   In the paper's words: any $L^p$ module is isometrically isomorphic, as a module, to a principal $L^p$ module. It generalizes the existence of orthonormal bases of Hilbert spaces ($p=2$) and Paschke's theorem for self-dual Hilbert C$^*$-modules ($p=\infty$).
--
--   **Formalization Note** The paper proves this for an arbitrary von Neumann algebra with Haagerup $L^p$ spaces, which are not available in Mathlib; this statement is the finite-dimensional case, where $L^p(\mathcal M)=\mathcal M$ with $\|a\|_p=(\mathrm{Tr}\,(a^*a)^{p/2})^{1/p}$. $p=\infty$ is out of scope. The module $\mathfrak X$ is arbitrary (of any dimension) and $I$ lives in the same universe as $\mathfrak X$. The norm on $\mathfrak X$ is the $p$-dependent trace norm of $\langle\xi,\xi\rangle^{1/2}$, not the C$^*$-module norm $\|\langle\xi,\xi\rangle\|^{1/2}$.
-- source:
--   Junge & Sherman, Noncommutative Lp modules, arXiv:math/0301044v2, p. 10, Theorem 2.5 (proof §3, pp. 11–16)

import Mathlib
import Definitions.Def_NCLpModules_Principal_Model

namespace NCLpModules.Principal

open scoped Matrix ComplexOrder

universe u

theorem theorem_2_5 {n : ℕ} (M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    {p : ℝ} (hp : 0 < p)
    {𝔛 : Type u} [AddCommGroup 𝔛] [Module ℂ 𝔛]
    (act : 𝔛 → Matrix (Fin n) (Fin n) ℂ → 𝔛) (ip : LpInnerProduct M 𝔛 act)
    (hX : IsLpModule p M act ip) :
    ∃ (ι : Type u) (q : ι → Matrix (Fin n) (Fin n) ℂ)
      (T : 𝔛 → ι → Matrix (Fin n) (Fin n) ℂ),
      (∀ α, IsProj M (q α)) ∧
      (∀ ξ, T ξ ∈ columnSumSet M q) ∧
      Function.Injective T ∧
      (∀ η ∈ columnSumSet M q, ∃ ξ, T ξ = η) ∧
      (∀ (c : ℂ) (ξ η : 𝔛), T (c • ξ + η) = c • T ξ + T η) ∧
      (∀ (ξ : 𝔛) (x : Matrix (Fin n) (Fin n) ℂ), x ∈ M →
        T (act ξ x) = fun α => T ξ α * x) ∧
      (∀ ξ : 𝔛, ipNorm p (colIp (T ξ) (T ξ)) = gauge p ip ξ) := by sorry

end NCLpModules.Principal
