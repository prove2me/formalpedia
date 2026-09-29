-- Prove2me | Theorems.Thm_ModularCurve_exists_addSubgroup_eisensteinTorsionBar_two_nsmul_surjOn_inertia_smul_eq_nat_smul_smul_sub_mem
-- name    : ModularCurve.exists_addSubgroup_eisensteinTorsionBar_two_nsmul_surjOn_inertia_smul_eq_nat_smul_smul_sub_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/e14012a0-4360-503a-be19-4e4b5dae7f55
-- title:
--   A 2-divisible multiplicative-type subgroup of dyadic Eisenstein torsion
-- statement:
--   Let $p$ be a prime and let $B$ be a valuation subring of $\overline{\mathbf Q}$ lying over $2$, i.e. such that $2$ is a non-unit of $B$. Then there is an additive subgroup $C$ of `JZero p`, the degree-zero divisor class group of the base change to $\overline{\mathbf Q}$ of the full modular function field of level $p$, with the following four properties. First, every $c \in C$ lies in `eisensteinTorsionBar p 2 M` for some $M$, that is, $c$ is annihilated by every element of the $M$-th power of the Eisenstein ideal $\mathfrak m = (\mathrm{eisensteinEval}\,p)^{-1}(2\mathbf Z)$ of the Hecke algebra `HeckeAlg` $= \mathbf Z[T_\ell : \ell \text{ prime}]$ acting through `heckeModuleBar`. Secondly, $C$ is $2$-divisible in itself: each $c \in C$ is of the form $2c'$ with $c' \in C$. Thirdly, for every $k$ and every function $n$ on $\mathrm{Gal}(\overline{\mathbf Q}/\mathbf Q)$ satisfying $\sigma\zeta = \zeta^{n(\sigma)}$ for all $\sigma$ and all $\zeta$ with $\zeta^{2^k} = 1$, every $\sigma$ in the inertia subgroup of $B$ over $\mathbf Q$ (the image of `B.inertiaSubgroup ℚ` in the full Galois group) acts on every $c \in C$ with $2^k c = 0$ by $\sigma \cdot c = n(\sigma)\,c$. Fourthly, $\sigma\cdot x - x \in C$ for every such $\sigma$, every $M$, and every $x \in$ `eisensteinTorsionBar p 2 M`.
--
--   This is the group-theoretic form, for the Jacobian of $X_0(p)$ over $\overline{\mathbf Q}$, of Mazur's statement that the connected component of the $2$-primary Eisenstein torsion of the Néron model over $\mathbf Z_2$ is of multiplicative type: the subgroup $C$ plays the role of the connected part, being $2$-divisible, cyclotomic for inertia at $2$, and absorbing all inertia displacements $\sigma x - x$ on the Eisenstein torsion. It is used in the construction of generators of the relevant Tate module and in the $2$-divisibility statement for elements of the inertia-displacement subgroup killed by a power of $2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_addSubgroup_eisensteinTorsionBar_two_nsmul_surjOn_inertia_smul_eq_nat_smul_smul_sub_mem.lean

import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.exists_addSubgroup_eisensteinTorsionBar_two_nsmul_surjOn_inertia_smul_eq_nat_smul_smul_sub_mem
    (p : ℕ) [Fact p.Prime]
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : B.LiesOverPrime 2) :
    ∃ C : AddSubgroup (JZero p),
      (∀ c ∈ C, ∃ M : ℕ, c ∈ eisensteinTorsionBar p 2 M) ∧
      (∀ c ∈ C, ∃ c' ∈ C, 2 • c' = c) ∧
      (∀ (k : ℕ) (n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ),
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
            ∀ ζ : AlgebraicClosure ℚ, ζ ^ (2 ^ k) = 1 → σ ζ = ζ ^ n σ) →
          ∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ c ∈ C, 2 ^ k • c = 0 → σ • c = n σ • c) ∧
      (∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ M : ℕ, ∀ x ∈ eisensteinTorsionBar p 2 M,
          σ • x - x ∈ C) := by sorry
