-- Prove2me | Theorems.Thm_ModularCurve_exists_multiplicativeTypeNat_torsionBySet_pow_inertiaSubgroupIn
-- name    : ModularCurve.exists_multiplicativeTypeNat_torsionBySet_pow_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/82ca1e09-fe1f-5f7a-8cf7-b541891d8cee
-- title:
--   Multiplicative-type subgroup inside the I^m-torsion of J₀(p)
-- statement:
--   Let $p$ and $q$ be primes with $q \neq p$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $q$ in the sense that $q$ belongs to the nonunits of $A$. Let $I$ be an ideal of the Hecke algebra `HeckeAlg` $= \mathbb{Z}[T_\ell : \ell \text{ prime}]$ (a polynomial ring on the set of primes) containing $q$, and suppose that for some $c \in \mathbb{N}$ one has $\mathfrak{P}^c \le I$, where $\mathfrak{P} =$ `eisensteinMaximalIdeal p q` is the preimage, under the evaluation of `HeckeAlg` at the Eisenstein system of level $p$, of the ideal $(q) \subseteq \mathbb{Z}$. Equip `JZero p`, the degree-zero divisor class group of the level-$p$ modular function field over $\overline{\mathbb{Q}}$, with its `HeckeAlg`-module structure `heckeModuleBar p`. The assertion is: for every $m \in \mathbb{N}$ and every function $n$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = (\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}})$ to $\mathbb{N}$ satisfying $\sigma\zeta = \zeta^{n(\sigma)}$ for all $\sigma$ and all $\zeta$ with $\zeta^{q^m} = 1$, there exists an additive subgroup $W \le$ `JZero p` such that: $W$ is contained in the submodule of elements annihilated by $I^m$; $W$ is of multiplicative type with character $n$ for the inertia subgroup `A.inertiaSubgroupIn ℚ` (the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of the decomposition subgroup of $A$), i.e. $\sigma \cdot x = n(\sigma) \cdot x$ for all $\sigma$ in that inertia subgroup and all $x \in W$; and $\sigma \cdot x - x \in W$ for every $\sigma$ in that inertia subgroup and every $x$ annihilated by $I^m$.
--
--   This is the $\mathbb{Z}/q$–$\mu_q$ admissibility of the Eisenstein-primary torsion of $J_0(p)$ at a prime $q \neq p$, in the form of a two-step filtration of the $I^m$-torsion whose graded pieces carry the trivial and the cyclotomic action of inertia at $q$. It is used in the analysis of the Néron-model torsion sheaf of $J_0(p)$, where the subgroup $W$ supplies the multiplicative-type piece against which the relevant filtration bound is read off.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_multiplicativeTypeNat_torsionBySet_pow_inertiaSubgroupIn.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_ModularCurve_MultiplicativeType
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.exists_multiplicativeTypeNat_torsionBySet_pow_inertiaSubgroupIn
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (I : Ideal HeckeAlg) (hqI : (q : HeckeAlg) ∈ I) (c : ℕ) (hI : eisensteinMaximalIdeal p q ^ c ≤ I) :
    letI := heckeModuleBar p
    ∀ m, ∀ n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ,
      (∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ m) = 1 → σ ζ = ζ ^ n σ) →
    ∃ W : AddSubgroup (JZero p),
      W ≤ (Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup ∧
      MultiplicativeTypeNat (A.inertiaSubgroupIn ℚ) n W ∧
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ (Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup,
        σ • (x : JZero p) - x ∈ W := by sorry
