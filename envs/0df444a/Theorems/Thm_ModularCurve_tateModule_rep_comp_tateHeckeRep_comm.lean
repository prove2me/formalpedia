-- Prove2me | Theorems.Thm_ModularCurve_tateModule_rep_comp_tateHeckeRep_comm
-- name    : ModularCurve.tateModule_rep_comp_tateHeckeRep_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/4a3d107c-b612-5fb6-b3f7-49efb8b089ba
-- title:
--   Galois and Hecke actions on T_q J₀(N) commute
-- statement:
--   Fix a natural number $N \neq 0$ and a prime $q$, let $\sigma$ be an automorphism of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` over $\mathbb Q$, and let $t$ be an element of the Hecke algebra `HeckeAlg`, i.e. of the polynomial ring $\mathbb Z[X_\ell : \ell \text{ prime}]$ in indeterminates indexed by the primes. The group $J_0(N) =$ `JZero N` is the degree-zero divisor class group $\mathrm{Pic}^0$ of the base-changed modular function field `modularFunctionFieldBar N` over $\overline{\mathbb Q}$, equipped with the `HeckeAlg`-module structure `heckeModuleBar N` (evaluation of polynomials at the operators `heckeOperatorBar N ℓ` when those commute, and the zero evaluation otherwise) and with its natural action of the automorphism group of $\overline{\mathbb Q}$. On the $q$-adic Tate module [`TateModule q (JZero N)`](def/EllipticCurve_TateModule.html#L15), consisting of the sequences $(x_n)_{n \in \mathbb N}$ in $J_0(N)$ with $q^n x_n = 0$ and $q\,x_{n+1} = x_n$, the conclusion is the conjunction of two commutation identities: first, the $\mathbb Z_q$-linear endomorphism given by the levelwise action of $\sigma$, [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174), commutes with the levelwise action `tateHeckeRep q (JZero N) t` of $t$; second, the corresponding identity after base change, for the $\mathbb Q_q$-linear operators `rationalGaloisRep` and `rationalHeckeRep` on $\mathbb Q_q \otimes_{\mathbb Z_q} T_q J_0(N)$.
--
--   This records that the Hecke correspondences on $J_0(N)$ are defined over $\mathbb Q$, so that the Hecke action on the $q$-adic Tate module is $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$-equivariant, in both its integral and its rational form. It is used to make operators coming from Galois elements (in particular inertia) Hecke-linear, in the statements about inertia-fixed vectors and Hecke-module independence in the Tate module of $J_0(N)$ that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_tateModule_rep_comp_tateHeckeRep_comm.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

set_option autoImplicit false

theorem ModularCurve.tateModule_rep_comp_tateHeckeRep_comm
    (N q : ℕ) [NeZero N] [Fact q.Prime] (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : HeckeAlg) :
    letI := heckeModuleBar N
    TateModule.rep q (JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ ∘ₗ tateHeckeRep q (JZero N) t =
      tateHeckeRep q (JZero N) t ∘ₗ TateModule.rep q (JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ ∧
    rationalGaloisRep q (JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ ∘ₗ rationalHeckeRep q (JZero N) t =
      rationalHeckeRep q (JZero N) t ∘ₗ rationalGaloisRep q (JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ := by sorry
