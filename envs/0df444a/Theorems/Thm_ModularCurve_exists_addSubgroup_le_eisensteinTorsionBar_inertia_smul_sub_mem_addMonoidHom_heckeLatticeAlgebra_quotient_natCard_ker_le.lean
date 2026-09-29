-- Prove2me | Theorems.Thm_ModularCurve_exists_addSubgroup_le_eisensteinTorsionBar_inertia_smul_sub_mem_addMonoidHom_heckeLatticeAlgebra_quotient_natCard_ker_le
-- name    : ModularCurve.exists_addSubgroup_le_eisensteinTorsionBar_inertia_smul_sub_mem_addMonoidHom_heckeLatticeAlgebra_quotient_natCard_ker_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/46214733-cccc-5c2e-a71e-0b110f990be7
-- title:
--   Hecke coordinate on inertia displacements in J₀(p)[P^m]
-- statement:
--   Let $p$ be a prime, let $B$ be a valuation subring of $\overline{\mathbb{Q}}$ which lies over $2$ in the sense that $2$ is a non-unit of $B$, and give the group $J_0(p) =$ `JZero p` of degree-zero divisor classes of the modular function field of level $p$ over $\overline{\mathbb{Q}}$ its module structure over `HeckeAlg` $= \mathbb{Z}[X_\ell : \ell \text{ prime}]$ coming from `heckeModuleBar p`. Then there is a single natural number $C$, independent of $m$, such that for every $m$ there is an additive subgroup $D$ of $J_0(p)$ with: $D$ is contained in `eisensteinTorsionBar p 2 m`, the subgroup of elements annihilated by the $m$-th power of the ideal `eisensteinMaximalIdeal p 2` of `HeckeAlg`; $D$ is stable under the action of every element of `HeckeAlg`; $D$ contains every displacement $\sigma \cdot x - x$ with $\sigma$ in the inertia subgroup of $B$ inside $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (the image of `B.inertiaSubgroup ℚ` under the inclusion of the decomposition subgroup) and $x$ in all of `eisensteinTorsionBar p 2 m`; and there is an additive homomorphism $\iota$ from $D$ to $\mathbb{T}/(2^m)$, where $\mathbb{T} =$ `heckeLatticeAlgebra p ∅` is the image of the Hecke algebra of weight-two cusp forms of level $p$ acting on the integral $q$-expansion lattice, such that $\iota(t \cdot x) = \overline{t}\,\iota(x)$ for $t$ in `HeckeAlg`, with $\overline{t}$ the class of the image of $t$ under `heckeEvalForms p 2` (sending the variable at $\ell$ to $U_\ell$ if $\ell \mid p$ and to $T_\ell$ otherwise) followed by `latticeRestrictHom p ∅`, and such that $\ker \iota$ is finite of cardinality at most $2^C$.
--
--   This is the form in which the rank-one Hecke coordinate on the $2$-adic inertia displacements inside the Eisenstein-primary torsion of $J_0(p)$ is used: the ambiguity of the coordinate is confined to a kernel of order bounded uniformly in $m$. It feeds the multiplicative-type step [`ModularCurve.exists_addMonoidHom_heckeLatticeAlgebra_quotient_two_pow_natCard_ker_le_of_multiplicativeTypeNat_le_eisensteinTorsionBar`](thm.html#ModularCurve.exists_addMonoidHom_heckeLatticeAlgebra_quotient_two_pow_natCard_ker_le_of_multiplicativeTypeNat_le_eisensteinTorsionBar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_addSubgroup_le_eisensteinTorsionBar_inertia_smul_sub_mem_addMonoidHom_heckeLatticeAlgebra_quotient_natCard_ker_le.lean

import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeEvalForms
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve CuspForm

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_addSubgroup_le_eisensteinTorsionBar_inertia_smul_sub_mem_addMonoidHom_heckeLatticeAlgebra_quotient_natCard_ker_le
    (p : ℕ) [Fact p.Prime]
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : B.LiesOverPrime 2) :
    letI := heckeModuleBar p
    ∃ C : ℕ, ∀ m : ℕ,
      ∃ D : AddSubgroup (JZero p),
        D ≤ eisensteinTorsionBar p 2 m ∧
        (∀ t : HeckeAlg, ∀ x ∈ D, t • x ∈ D) ∧
        (∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ x ∈ eisensteinTorsionBar p 2 m,
          σ • x - x ∈ D) ∧
        ∃ ι : ↥D →+ (↥(heckeLatticeAlgebra p ∅) ⧸
              Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m}),
          (∀ (t : HeckeAlg) (x : ↥D) (htx : t • (x : JZero p) ∈ D),
            ι ⟨t • (x : JZero p), htx⟩ =
              Ideal.Quotient.mk (Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m})
                (((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) t) * ι x) ∧
          Nat.card ↥ι.ker ≤ 2 ^ C := by sorry
