-- Prove2me | Theorems.Thm_ModularCurve_exists_addMonoidHom_heckeLatticeAlgebra_quotient_two_pow_natCard_ker_le_of_multiplicativeTypeNat_le_eisensteinTorsionBar
-- name    : ModularCurve.exists_addMonoidHom_heckeLatticeAlgebra_quotient_two_pow_natCard_ker_le_of_multiplicativeTypeNat_le_eisensteinTorsionBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/daad3af6-e5cb-540f-aa9b-635810ce27a7
-- title:
--   Hecke coordinate on multiplicative-type subgroups of J₀(p)[P^m] at 2
-- statement:
--   Let $p$ be a prime and let $B$ be a valuation subring of $\overline{\mathbb{Q}}=$ `AlgebraicClosure ℚ` lying over $2$, in the sense that $2$ is a nonunit of $B$; the group $J_0(p)=$ `JZero p`, the degree-zero divisor class group of the modular function field of level $p$ over $\overline{\mathbb{Q}}$, carries the `HeckeAlg` $=\mathbb{Z}[X_\ell : \ell \text{ prime}]$-module structure `heckeModuleBar p`. The assertion is that there is a natural number $C$, independent of everything below, such that for every $m$, every function $n$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\mathbb{N}$ with $\sigma\zeta = \zeta^{n(\sigma)}$ for all $\sigma$ and all $\zeta$ with $\zeta^{2^m}=1$, and every additive subgroup $W \le J_0(p)$ contained in `eisensteinTorsionBar p 2 m` (the elements annihilated by every element of the $m$-th power of the ideal `eisensteinMaximalIdeal p 2` of `HeckeAlg`) and of multiplicative type for $n$ along the inertia subgroup of $B$ over $\mathbb{Q}$, i.e. $\sigma \cdot x = n(\sigma)\, x$ for all $\sigma$ in that inertia subgroup and all $x \in W$, there is an additive homomorphism $g$ from $W$ to $\mathbb{T}^L/(2^m)$, where $\mathbb{T}^L =$ `heckeLatticeAlgebra p ∅` is the image of the weight-two level-$p$ Hecke algebra in $\mathrm{End}_{\mathbb{Z}}$ of the lattice of cusp forms with integral $q$-expansion, such that $g(t \cdot z) = \overline{\lambda(t)}\, g(z)$ whenever $t \in$ `HeckeAlg`, $z \in W$ and $t \cdot z \in W$, with $\lambda$ the map sending each variable $X_\ell$ to $U_\ell$ if $\ell \mid p$ and to $T_\ell$ otherwise and then to its action on the lattice, and such that $\#\ker g \le 2^C$.
--
--   This is the rank-one Hecke coordinate on Hecke-stable subgroups of the Eisenstein torsion of $J_0(p)$ which are of multiplicative type at a place above $2$, in the spirit of Mazur's study of the Eisenstein ideal. It is used in the variant [`ModularCurve.exists_addMonoidHom_inf_ker_reductionModL_eisensteinTorsionBar_heckeLatticeAlgebra_quotient_two_pow_natCard_ker_le`](thm.html#ModularCurve.exists_addMonoidHom_inf_ker_reductionModL_eisensteinTorsionBar_heckeLatticeAlgebra_quotient_two_pow_natCard_ker_le), where the coordinate is restricted further to a kernel of reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_addMonoidHom_heckeLatticeAlgebra_quotient_two_pow_natCard_ker_le_of_multiplicativeTypeNat_le_eisensteinTorsionBar.lean

import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeEvalForms
import Definitions.Def_ModularCurve_MultiplicativeType
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve CuspForm

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_addMonoidHom_heckeLatticeAlgebra_quotient_two_pow_natCard_ker_le_of_multiplicativeTypeNat_le_eisensteinTorsionBar
    (p : ℕ) [Fact p.Prime]
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : B.LiesOverPrime 2) :
    letI := heckeModuleBar p
    ∃ C : ℕ, ∀ m : ℕ,
      ∀ n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ,
        (∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (2 ^ m) = 1 → σ ζ = ζ ^ n σ) →
      ∀ W : AddSubgroup (JZero p), W ≤ eisensteinTorsionBar p 2 m →
        MultiplicativeTypeNat (B.inertiaSubgroupIn ℚ) n W →
      ∃ g : ↥W →+ (↥(heckeLatticeAlgebra p ∅) ⧸
            Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m}),
        (∀ (t : HeckeAlg) (z : ↥W) (htz : t • (z : JZero p) ∈ W),
          g ⟨t • (z : JZero p), htz⟩ =
            Ideal.Quotient.mk (Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m})
              (((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) t) * g z) ∧
        Nat.card ↥g.ker ≤ 2 ^ C := by sorry
