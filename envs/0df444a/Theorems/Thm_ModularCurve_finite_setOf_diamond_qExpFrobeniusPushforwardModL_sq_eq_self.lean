-- Prove2me | Theorems.Thm_ModularCurve_finite_setOf_diamond_qExpFrobeniusPushforwardModL_sq_eq_self
-- name    : ModularCurve.finite_setOf_diamond_qExpFrobeniusPushforwardModL_sq_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/c34ac2a7-1bef-5d06-bcdc-a6f6452b1f11
-- title:
--   Finiteness of the fixed locus of ⟨ ̄ p⟩ ∘ F²
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ but $p^{2} \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and an algebraically closed field $\kappa$ of characteristic $p$ which is assumed to satisfy: for every $a \in \kappa$ there is $n > 0$ with $a^{p^{n}} = a$ (so $\kappa$ is algebraic over $\mathbb{F}_{p}$). Write $P = \mathrm{Pic}^{0}$ of the field `Fbar p M H hpM κ` $=$ `qExpFunctionFieldC κ (ΓN p M H hpM)` over $\kappa$, i.e. the group of degree-zero elements of the free abelian group on the places of this function field over $\kappa$, modulo the subgroup of principal divisors. Let $F : P \to P$ be an additive endomorphism agreeing pointwise with `qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p`, the Frobenius push-forward on $P$ (given by `qExpFrobeniusPic0PushforwardModL` when the input predicate `QExpFrobeniusInputsModL` holds for these data, and by $0$ otherwise). Let $pb \in (\mathbb{Z}/(M/p))^{\times}$, and let $\delta : P \to P$ be an additive endomorphism agreeing pointwise with the action on $P$, through `SemilinearAut.ofAlgAut`, of the $\kappa$-algebra automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at the chosen lift [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $pb$ to $\Gamma_{0}(M/p)$, where `infSubgroup p M H hpM` is the image of $H$ in $(\mathbb{Z}/(M/p))^{\times}$ under reduction; that is, $\delta$ is the diamond operator $\langle pb \rangle$ at level $\Gamma_{H'}(M/p)$. The conclusion is that the set $\{ z \in P : \delta(F(F(z))) = z \}$ is finite.
--
--   This is the finiteness of the eigenvalue-one locus of $\langle \bar p\rangle_{*} \circ F^{2}$ on the degree-zero divisor class group of the level-$\Gamma_{H'}(M/p)$ function field in characteristic $p$, the input needed to show that a class annihilated by one factor of the characteristic polynomial of the push–pull matrix on the special fibre is torsion. It is used in [`ModularCurve.JHNeronObjectAtP.exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero`](thm.html#ModularCurve.JHNeronObjectAtP.exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finite_setOf_diamond_qExpFrobeniusPushforwardModL_sq_eq_self.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

theorem ModularCurve.finite_setOf_diamond_qExpFrobeniusPushforwardModL_sq_eq_self
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p]

    (halg : ∀ a : κ, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)
    (F : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p z)
    (pb : (ZMod (M / p))ˣ)
    (δ : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL κ (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z) :
    {z : Pic0 κ (Fbar p M H hpM κ) | δ (F (F z)) = z}.Finite := by sorry
