-- Prove2me | Theorems.Thm_Module_End_maxGenEigenspace_baseChange_le_eigenspace_of_isAlgClosed
-- name    : Module.End.maxGenEigenspace_baseChange_le_eigenspace_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/760b96c1-c996-594f-b47b-3726e7f002ec
-- title:
--   Semisimplicity of a base change descends and spreads to all extensions
-- statement:
--   Let $K$ be a field of characteristic zero, $W$ a finite-dimensional $K$-vector space, and $T$ a $K$-linear endomorphism of $W$. For a field extension $\Omega$ of $K$, write $T_\Omega$ for the base change `T.baseChange Ω`, the $\Omega$-linear endomorphism of $\Omega \otimes_K W$ induced by $T$; recall that `Module.End.eigenspace` of $T_\Omega$ at $\mu \in \Omega$ is $\ker(T_\Omega - \mu)$ and `Module.End.maxGenEigenspace` at $\mu$ is the supremum $\bigcup_k \ker\bigl((T_\Omega - \mu)^k\bigr)$ over all natural numbers $k$. The hypothesis is that for one algebraically closed field extension $\Omega_1$ of $K$ and every $\mu \in \Omega_1$, the maximal generalised eigenspace of $T_{\Omega_1}$ at $\mu$ is contained in the eigenspace of $T_{\Omega_1}$ at $\mu$, i.e. every generalised eigenvector of $T_{\Omega_1}$ is an eigenvector. The conclusion is that for an arbitrary field extension $\Omega_2$ of $K$ — not assumed algebraically closed — and an arbitrary $\mu \in \Omega_2$, the maximal generalised eigenspace of $T_{\Omega_2}$ at $\mu$ is likewise contained in $\ker(T_{\Omega_2} - \mu)$.
--
--   This is the statement that the semisimplicity of $T$, expressed as the coincidence of eigenspaces with maximal generalised eigenspaces after base change, is independent of the extension field in which eigenvalues are taken: testing over a single algebraically closed extension suffices. It is used in the computation of the dimension of the simultaneous Hecke eigenspace in [`CohCarrier.finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity`](thm.html#CohCarrier.finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity), where generalised eigenspaces over one coefficient field have to be replaced by honest eigenspaces over another.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_End_maxGenEigenspace_baseChange_le_eigenspace_of_isAlgClosed.lean

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.End.maxGenEigenspace_baseChange_le_eigenspace_of_isAlgClosed
    {K : Type} [Field K] [CharZero K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (T : Module.End K W)
    (Ω₁ : Type) [Field Ω₁] [Algebra K Ω₁] [IsAlgClosed Ω₁]
    (h₁ : ∀ μ : Ω₁, Module.End.maxGenEigenspace (T.baseChange Ω₁) μ ≤
      Module.End.eigenspace (T.baseChange Ω₁) μ)
    (Ω₂ : Type) [Field Ω₂] [Algebra K Ω₂] (μ : Ω₂) :
    Module.End.maxGenEigenspace (T.baseChange Ω₂) μ ≤ Module.End.eigenspace (T.baseChange Ω₂) μ := by sorry
