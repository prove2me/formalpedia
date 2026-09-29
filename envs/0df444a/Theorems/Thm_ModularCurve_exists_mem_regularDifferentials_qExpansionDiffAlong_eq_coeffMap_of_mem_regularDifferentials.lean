-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_regularDifferentials_qExpansionDiffAlong_eq_coeffMap_of_mem_regularDifferentials
-- name    : ModularCurve.exists_mem_regularDifferentials_qExpansionDiffAlong_eq_coeffMap_of_mem_regularDifferentials
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/78ff1229-c5df-526e-855e-f02fca7d6727
-- title:
--   Regular differentials and q-expansions under constant field change
-- statement:
--   Let $\iota\colon\kappa\to k$ be a ring homomorphism of fields with $k$ perfect, and let $N\ge 1$ be an integer whose image in $k$ is nonzero. For a field $K$ write $F_K=K(j(q),j(q^N))$ for the intermediate field `modularFunctionFieldC K N` of the Laurent series field $K((q))$, namely the subfield generated over $K$ by `jqModC K` $=q^{-1}\cdot(\text{the integral power series }j\mathrm{Num}\text{ mapped into }K)$ and by its $N$-fold $q$-substitution `jqNModC K N`. Call a Kähler differential of $F_K/K$ regular when for every place $v$ of $F_K$ over $K$ — a valuation subring $\mathcal O_v\neq F_K$ containing $K$ and a principal ideal ring — it is of the form $f\cdot d\pi_v$ with $f\in\mathcal O_v$ and $\pi_v$ the chosen uniformiser at $v$. Let $\Theta_K$ denote `qExpansionDiffAlong` of the inclusion $F_K\hookrightarrow K((q))$, the $K$-linear map on $\Omega[F_K/K]$ characterised by $\Theta_K(d x)=\theta(x)$ and $\Theta_K(f\cdot\omega)=f\,\Theta_K(\omega)$ (and $0$ if no such map exists). The assertion is: for every regular differential $\omega_0$ of $F_\kappa/\kappa$ there exists a regular differential $\omega$ of $F_k/k$ with $\Theta_k(\omega)$ equal to the Laurent series obtained from $\Theta_\kappa(\omega_0)$ by applying $\iota$ to each coefficient.
--
--   This is the compatibility of the space of regular differentials on $X_0(N)$, together with the $q$-expansion map, with extension of the constant field. It serves to transport differentials attached to cusp forms from the constant fields over which they are first constructed to an arbitrary perfect field in which $N$ is invertible, and is used by [`ModularCurve.exists_mem_regularDifferentials_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast`](thm.html#ModularCurve.exists_mem_regularDifferentials_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_regularDifferentials_qExpansionDiffAlong_eq_coeffMap_of_mem_regularDifferentials.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.exists_mem_regularDifferentials_qExpansionDiffAlong_eq_coeffMap_of_mem_regularDifferentials
    {κ k : Type*} [Field κ] [Field k] [PerfectField k] (ι : κ →+* k)
    (N : ℕ) [NeZero N] (hN : (N : k) ≠ 0)
    (ω₀ : Ω[modularFunctionFieldC κ N⁄κ])
    (hω₀ : ω₀ ∈ regularDifferentials κ (modularFunctionFieldC κ N)) :
    ∃ ω ∈ regularDifferentials k (modularFunctionFieldC k N),
      qExpansionDiffAlong (modularFunctionFieldC k N).val ω =
        coeffMap ι (qExpansionDiffAlong (modularFunctionFieldC κ N).val ω₀) := by sorry
