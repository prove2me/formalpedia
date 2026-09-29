-- Prove2me | Theorems.Thm_ModularCurve_inertia_smul_eq_nsmul_of_forall_exists_heckeOperatorBar_pow_apply_eq_of_reductionModL_eq_zero_of_ne_two
-- name    : ModularCurve.inertia_smul_eq_nsmul_of_forall_exists_heckeOperatorBar_pow_apply_eq_of_reductionModL_eq_zero_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/11a52631-be82-5236-9fed-3e26ad2459aa
-- title:
--   Inertia acts cyclotomically on ordinary λ-torsion reducing to zero
-- statement:
--   Fix a positive integer $M$ and a prime $\lambda$ with $\lambda \nmid M$ and $\lambda \neq 2$, and a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime lam`, i.e. $\lambda$ is a nonunit of $A$. The assertion is: for every natural number $k$ and every function $n$ from $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q}) = (\overline{\mathbb{Q}} \simeq_{\mathrm{alg}[\mathbb{Q}]} \overline{\mathbb{Q}})$ to $\mathbb{N}$ such that $\sigma\zeta = \zeta^{n(\sigma)}$ for every $\sigma$ and every $\zeta \in \overline{\mathbb{Q}}$ with $\zeta^{\lambda^k} = 1$, and for every element $v$ of `JZero M`, the group of degree-zero divisor classes of the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $M$, the following holds. Suppose that for every $m$ there is a $z \in$ `JZero M` with $\lambda^k \cdot z = 0$ and $(\mathrm{heckeOperatorBar}\,M\,\lambda)^m z = v$, where `heckeOperatorBar` is the $\mathbb{Z}$-linear endomorphism of `JZero M` given by `heckeOperatorAlong` at $\lambda$ (so, taking $m = 0$, $v$ itself is killed by $\lambda^k$ and lies in all iterated images of $T_\lambda$), and suppose that `reductionModL A M v = 0`, the reduction of $v$ along the residue map of $A$ as defined by `reductionAlong`. Then $\sigma \bullet v = n(\sigma)\cdot v$ for every $\sigma$ in `A.inertiaSubgroupIn ℚ`, the image in $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of the decomposition subgroup of $A$.
--
--   This is the statement that the $T_\lambda$-ordinary part of the $\lambda^k$-torsion of the Jacobian of level $M$ that reduces to zero at a place above $\lambda$ is of multiplicative type, so that inertia acts on it through the cyclotomic character mod $\lambda^k$; it rests on the Eichler–Shimura relation $T_\lambda = F + V$ on the special fibre. It is used in the analysis of the kernel of reduction modulo $\lambda$ and of the ordinary filtration of the Hecke torsion, feeding the local conditions at $\lambda$ required for level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_inertia_smul_eq_nsmul_of_forall_exists_heckeOperatorBar_pow_apply_eq_of_reductionModL_eq_zero_of_ne_two.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_ReductionModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.inertia_smul_eq_nsmul_of_forall_exists_heckeOperatorBar_pow_apply_eq_of_reductionModL_eq_zero_of_ne_two
    (M : ℕ) [NeZero M] (lam : ℕ) [Fact lam.Prime] (hlamM : ¬ lam ∣ M) (hlam2 : lam ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (_hA : A.LiesOverPrime lam) :
    ∀ k : ℕ, ∀ n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ,
      (∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (lam ^ k) = 1 → σ ζ = ζ ^ n σ) →
      ∀ v : JZero M,
        (∀ m : ℕ, ∃ z : JZero M, lam ^ k • z = 0 ∧
          (heckeOperatorBar M ⟨lam, Fact.out⟩ ^ m) z = v) →
        reductionModL A M v = 0 →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • v = n σ • v := by sorry
