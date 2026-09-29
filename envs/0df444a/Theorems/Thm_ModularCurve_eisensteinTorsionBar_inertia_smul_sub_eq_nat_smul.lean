-- Prove2me | Theorems.Thm_ModularCurve_eisensteinTorsionBar_inertia_smul_sub_eq_nat_smul
-- name    : ModularCurve.eisensteinTorsionBar_inertia_smul_sub_eq_nat_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/4e3ed97d-dce4-5e88-b129-e6560a2091a8
-- title:
--   Inertia at q≠ p acts on Eisenstein displacements cyclotomically
-- statement:
--   Fix primes $p$ and $q$ with $q \neq p$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $q$, in the sense that $q$, viewed in $\overline{\mathbb{Q}}$, is a nonunit of $A$. Write $J =$ `JZero p` for the degree-zero divisor classes modulo principal divisors of the base change to $\overline{\mathbb{Q}}$ of the modular function field of level $p$, with its $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$-action and its `HeckeAlg` $=\mathbb{Z}[T_\ell : \ell \text{ prime}]$-module structure `heckeModuleBar p`. The assertion is: for every $m \in \mathbb{N}$ and every function $n$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\mathbb{N}$ which computes the action on $q^m$-th roots of unity, i.e. $\sigma\zeta = \zeta^{n(\sigma)}$ whenever $\zeta^{q^m} = 1$, and for every $\sigma$ in the inertia subgroup of $A$ (the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup inside the decomposition subgroup of $A$), every $x$ annihilated by the $m$-th power of the Eisenstein ideal `eisensteinMaximalIdeal p q` — the pullback along `eisensteinEval p` of the ideal $(q) \subseteq \mathbb{Z}$ — and every $\tau$ in that same inertia subgroup, one has $\tau \cdot (\sigma x - x) = n(\tau)\,(\sigma x - x)$ in $J$.
--
--   This is the point-level form of the statement that the Eisenstein torsion of $J_0(p)$ is ordinary at a prime $q \neq p$, the displacements $\sigma x - x$ under inertia lying in the part on which inertia acts through the cyclotomic character; the case $q = 2$ is supplied separately by [`ModularCurve.eisensteinTorsionBar_inertia_smul_sub_eq_nat_smul_two`](thm.html#ModularCurve.eisensteinTorsionBar_inertia_smul_sub_eq_nat_smul_two). It feeds the construction of the multiplicative-type subgroups and quotients of the Eisenstein torsion used later, being cited by [`ModularCurve.exists_multiplicativeTypeNat_torsionBySet_pow_inertiaSubgroupIn`](thm.html#ModularCurve.exists_multiplicativeTypeNat_torsionBySet_pow_inertiaSubgroupIn), [`ModularCurve.exists_submodule_multiplicativeTypeNat_maximal_heckeTorsion_span_sup_inertiaSubgroupIn`](thm.html#ModularCurve.exists_submodule_multiplicativeTypeNat_maximal_heckeTorsion_span_sup_inertiaSubgroupIn) and [`ModularCurve.exists_addMonoidHom_eisensteinTorsionBar_inf_closure_inertia_smul_sub_heckeLatticeAlgebra_quotient_natCard_ker_le`](thm.html#ModularCurve.exists_addMonoidHom_eisensteinTorsionBar_inf_closure_inertia_smul_sub_heckeLatticeAlgebra_quotient_natCard_ker_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eisensteinTorsionBar_inertia_smul_sub_eq_nat_smul.lean

import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.eisensteinTorsionBar_inertia_smul_sub_eq_nat_smul
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (_hA : A.LiesOverPrime q) :
    ∀ m, ∀ n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ,
      (∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ m) = 1 → σ ζ = ζ ^ n σ) →
    ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ eisensteinTorsionBar p q m,
      ∀ τ ∈ A.inertiaSubgroupIn ℚ,
        τ • (σ • (x : JZero p) - x) = n τ • (σ • (x : JZero p) - x) := by sorry
