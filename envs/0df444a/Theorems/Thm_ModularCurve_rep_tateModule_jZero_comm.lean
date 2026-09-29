-- Prove2me | Theorems.Thm_ModularCurve_rep_tateModule_jZero_comm
-- name    : ModularCurve.rep_tateModule_jZero_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/af0e0ee7-bbcc-5ee3-b6df-36845a23c9c9
-- title:
--   Galois and Hecke actions commute on Tₚ J₀(N)
-- statement:
--   Fix $N \ge 1$ and a prime $p$. Write $J_0(N)$ for [`ModularCurve.JZero N`](def/ModularCurve_ArithmeticGalois.html#L115), the group $\mathrm{Pic}^0$ of degree-zero divisor classes of the function field `modularFunctionFieldBar N` (the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$) over $\overline{\mathbb Q}$, carrying its natural action of $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q}) = \overline{\mathbb Q} \simeq_{\mathrm{alg}[\mathbb Q]} \overline{\mathbb Q}$. Assume `HeckeOperatorsCommuteBar N`: the endomorphisms `heckeOperatorBar N ℓ` of $J_0(N)$, for $\ell$ ranging over the primes, commute pairwise. The Hecke algebra is `HeckeAlg` $= \mathbb Z[X_\ell : \ell \text{ prime}]$ (a multivariate polynomial ring indexed by the primes), acting on $J_0(N)$ through the module structure `heckeModuleBar N`, which under the commutation hypothesis sends $X_\ell$ to `heckeOperatorBar N ℓ`. Both actions are transported coordinatewise by [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174) to the $p$-adic Tate module [`TateModule p (JZero N)`](def/EllipticCurve_TateModule.html#L15), the group of sequences $(x_n)_{n \in \mathbb N}$ in $J_0(N)$ with $p^n x_n = 0$ and $p\, x_{n+1} = x_n$. The assertion is that for every $\sigma \in \mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$, every $T \in$ `HeckeAlg` and every $x$ in this Tate module, $\sigma(Tx) = T(\sigma x)$.
--
--   This is the $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$-equivariance of the Hecke operators on the $p$-adic Tate module of $J_0(N)$, which makes $T_p J_0(N)$ a module over the Hecke algebra and the Galois group simultaneously. It is used in the construction of the $p$-adic Galois representation attached to a newform, notably by the results computing Frobenius traces and determinants on Hecke eigenplanes in $T_p J_0(N)$ and by the existence statement for the associated quadratic Frobenius relation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_rep_tateModule_jZero_comm.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.rep_tateModule_jZero_comm (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hcomm : ModularCurve.HeckeOperatorsCommuteBar N)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (T : ModularCurve.HeckeAlg)
    (x : TateModule p (ModularCurve.JZero N)) :
    letI := ModularCurve.heckeModuleBar N
    TateModule.rep p (ModularCurve.JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
        (TateModule.rep p (ModularCurve.JZero N) ModularCurve.HeckeAlg T x)
      = TateModule.rep p (ModularCurve.JZero N) ModularCurve.HeckeAlg T
        (TateModule.rep p (ModularCurve.JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x) := by sorry
