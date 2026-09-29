-- Prove2me | Theorems.Thm_ModularCurve_inertia_smul_eq_nsmul_of_forall_exists_heckeOperatorBar_pow_apply_eq_of_reductionModL_eq_zero
-- name    : ModularCurve.inertia_smul_eq_nsmul_of_forall_exists_heckeOperatorBar_pow_apply_eq_of_reductionModL_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/0f200390-754f-5380-bdab-8f7bfb24ca33
-- title:
--   Inertia acts cyclotomically on reducing T_λ-ordinary λ-power torsion
-- statement:
--   Fix a positive integer $M$ (nonzero as a natural number), a prime $\lambda$ not dividing $M$, and a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $\lambda$ in the sense that $\lambda$, viewed in $\overline{\mathbb{Q}}$, is a nonunit of $A$. The assertion is then: for every natural number $k$ and every function $n$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = (\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}})$ to $\mathbb{N}$ such that $\sigma\zeta = \zeta^{n(\sigma)}$ for every $\sigma$ and every $\zeta \in \overline{\mathbb{Q}}$ with $\zeta^{\lambda^k} = 1$ (so that $n$ realises the cyclotomic character modulo $\lambda^k$), and for every element $v$ of `JZero M`, the degree-zero Picard group $\mathrm{Pic}^0$ of the base change to $\overline{\mathbb{Q}}$ of the modular function field of level $M$, the following holds: if for every $m \in \mathbb{N}$ there exists $z \in$ `JZero M` with $\lambda^k \cdot z = 0$ and $(\mathrm{heckeOperatorBar}\,M\,\lambda)^m z = v$, where `heckeOperatorBar M ⟨lam, _⟩` is the $\mathbb{Z}$-linear Hecke endomorphism $T_\lambda$ of `JZero M`, and if `reductionModL A M v = 0`, i.e. $v$ dies under the reduction homomorphism to the degree-zero Picard group `JZeroC` of the modular curve over the residue field of $A$, then $\sigma \cdot v = n(\sigma) \cdot v$ for every $\sigma$ in `A.inertiaSubgroupIn ℚ`, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup inside the decomposition subgroup of $A$.
--
--   This is the formal counterpart of Mazur's description of the $T_\lambda$-ordinary part of the $\lambda$-power torsion of $J_0(M)$ at a prime $\lambda$ of good reduction: the connected part, i.e. the part reducing to zero, is of multiplicative type, so inertia acts on it through the cyclotomic character. It is used in the multiplicity-one estimate [`CuspForm.IsNewform.finrank_le_one_of_le_reductionKernelSpan_tateModule_jZero_of_isUnit`](thm.html#CuspForm.IsNewform.finrank_le_one_of_le_reductionKernelSpan_tateModule_jZero_of_isUnit), and its proof goes through a finite flat Hopf-algebra model of the relevant torsion together with the Eichler–Shimura relation $T_\lambda = F + V$ on the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_inertia_smul_eq_nsmul_of_forall_exists_heckeOperatorBar_pow_apply_eq_of_reductionModL_eq_zero.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_ReductionModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.inertia_smul_eq_nsmul_of_forall_exists_heckeOperatorBar_pow_apply_eq_of_reductionModL_eq_zero
    (M : ℕ) [NeZero M] (lam : ℕ) [Fact lam.Prime] (hlamM : ¬ lam ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (_hA : A.LiesOverPrime lam) :
    ∀ k : ℕ, ∀ n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ,
      (∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (lam ^ k) = 1 → σ ζ = ζ ^ n σ) →
      ∀ v : JZero M,
        (∀ m : ℕ, ∃ z : JZero M, lam ^ k • z = 0 ∧
          (heckeOperatorBar M ⟨lam, Fact.out⟩ ^ m) z = v) →
        reductionModL A M v = 0 →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • v = n σ • v := by sorry
