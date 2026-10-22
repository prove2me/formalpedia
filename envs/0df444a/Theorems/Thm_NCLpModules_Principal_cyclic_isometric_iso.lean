-- Prove2me | Theorems.Thm_NCLpModules_Principal_cyclic_isometric_iso
-- name    : NCLpModules.Principal.cyclic_isometric_iso
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:03.753896+00:00
-- url     : https://prove2.me/theorems/3d103a1a-16e4-4718-8692-261b4f3bacd8
-- title:
--   Theorem 2.5, cyclic case, pp. 10–11 — 𝔛 = ξM ≅ s(⟨ξ,ξ⟩^{1/2})L^p via ξx ↦ ⟨ξ,ξ⟩^{1/2}x
-- statement:
--   Let $\mathcal M\subseteq M_n(\mathbb C)$ be a unital $*$-subalgebra and $\mathfrak X$ a right $\mathcal M$-module with an $L^{p/2}$-valued inner product which is **cyclic**: there is $\xi\in\mathfrak X$ with $\mathfrak X=\xi\mathcal M=\{\xi x:x\in\mathcal M\}$. Put $A=\langle\xi,\xi\rangle$. Then there is a map $T:\mathfrak X\to L^p(\mathcal M)$ with
--   $$T(\xi x)=A^{1/2}x\qquad(x\in\mathcal M)$$
--   which is a bijection of $\mathfrak X$ onto $s(A^{1/2})L^p=\{s(A^{1/2})y:y\in\mathcal M\}$, is complex linear and right $\mathcal M$-linear ($T(\eta x)=T(\eta)x$), and preserves the inner product: $T(\eta)^*T(\eta')=\langle\eta,\eta'\rangle$. In particular $T$ is isometric for $\|\cdot\|=\|\langle\cdot,\cdot\rangle^{1/2}\|_p$ for every $p$.
--
--   This is the easy case of Theorem 2.5: a cyclic $L^p$ module is a principal module with a single projection $s(\langle\xi,\xi\rangle^{1/2})$.
--
--   **Formalization Note** Finite-dimensional scope. The page takes $\mathfrak X=\overline{\xi\mathcal M}$; here $\xi\mathcal M$ is a finite-dimensional subspace, hence closed, and the overline is dropped, so the "densely-defined" map is already defined everywhere. "Isomorphism of $L^p$ modules" is encoded as a bijective, $\mathbb C$-linear, right $\mathcal M$-linear map preserving the inner product $\langle a,b\rangle=a^*b$ of $L^p(\mathcal M)$. Completeness is automatic and not assumed. $A^{1/2}$ is `cfc Real.sqrt A` and $s(\cdot)$ is `supportProj`.
-- source:
--   Junge & Sherman, Noncommutative Lp modules, arXiv:math/0301044v2, pp. 10–11, after Theorem 2.5: 'If 𝔛 is cyclic, this is easy …'

import Mathlib
import Definitions.Def_NCLpModules_Principal_Model

namespace NCLpModules.Principal

open scoped Matrix ComplexOrder

theorem cyclic_isometric_iso {n : ℕ} (M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    {𝔛 : Type*} [AddCommGroup 𝔛] [Module ℂ 𝔛]
    (act : 𝔛 → Matrix (Fin n) (Fin n) ℂ → 𝔛) (hact : IsRightModuleAction M 𝔛 act)
    (ip : LpInnerProduct M 𝔛 act) (ξ : 𝔛)
    (hcyc : ∀ η : 𝔛, ∃ x ∈ M, η = act ξ x) :
    ∃ T : 𝔛 → Matrix (Fin n) (Fin n) ℂ,
      (∀ x ∈ M, T (act ξ x) = cfc Real.sqrt (ip.ip ξ ξ) * x) ∧
      (∀ η : 𝔛, ∃ y ∈ M, T η = supportProj (cfc Real.sqrt (ip.ip ξ ξ)) * y) ∧
      Function.Injective T ∧
      (∀ y ∈ M, ∃ η : 𝔛, T η = supportProj (cfc Real.sqrt (ip.ip ξ ξ)) * y) ∧
      (∀ (c : ℂ) (η η' : 𝔛), T (c • η + η') = c • T η + T η') ∧
      (∀ (η : 𝔛) (x : Matrix (Fin n) (Fin n) ℂ), x ∈ M → T (act η x) = T η * x) ∧
      (∀ η η' : 𝔛, (T η)ᴴ * T η' = ip.ip η η') := by sorry

end NCLpModules.Principal
