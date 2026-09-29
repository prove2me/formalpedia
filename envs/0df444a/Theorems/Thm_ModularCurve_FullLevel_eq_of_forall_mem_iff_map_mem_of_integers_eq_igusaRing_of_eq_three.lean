-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing_of_eq_three
-- name    : ModularCurve.FullLevel.eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/651eb8be-7f17-59d8-8966-871208fd1eaf
-- title:
--   Uniqueness of a place over a supersingular place, q=3
-- statement:
--   Let $q$ be a prime with $q = 3$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ belongs to the nonunits of $A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ over the residue field of $A$ whose members are exactly the supersingular places, i.e. the rational affine geometric places at which the value of the generator $j$-function lies in the supersingular $j$-set. Assume $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ as intermediate fields of $\overline{\mathbb{Q}}((X))$ over $\overline{\mathbb{Q}}$, the first being the base change to $\overline{\mathbb{Q}}$ of the level-$M'$ full modular function field, the second the $X_H$-field for level $q^2M'$ with $H$ the kernel of reduction of units mod $q$. Let $R_0$ be a constant reduction of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$: a valuation subring $R_0.\mathrm{integers}$ together with a surjective residue map onto the target whose kernel is the maximal ideal, compatible with $A$ on constants, admitting scalings making any nonzero element integral with nonzero residue, and equipped with a degree-preserving map on places compatible with push-forward of principal divisors. Assume further that for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb{Q}}((X))$ lies in $\mathrm{modularFunctionFieldBar}\,M'$, that element is $R_0$-integral and its residue, read as a Laurent series over $\mathrm{ResidueField}\,A$, is the coefficientwise reduction of $y$. Let $\zeta$ be a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$, and let $\ell \mapsto \mathcal{O}^{\mathrm{Ig}}_\ell$ assign a valuation subring of $\mathrm{fieldBar}\,q\,M'$ to each point of the projective line over $\mathbb{Z}/q$, subject to: the subring at the point $\infty$ consists of those $f$ whose Laurent expansion can be written as a quotient $x/y$ of coefficientwise images of Laurent series over $A$ with $y$ having nonzero reduction; and for each $\ell$ there is $\gamma \in \Gamma_0(M')$ whose reduction mod $q$ carries $\infty$ to $\ell$ and with $\mathcal{O}^{\mathrm{Ig}}_\ell$ the preimage of $\mathcal{O}^{\mathrm{Ig}}_\infty$ under the automorphism $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$. Fix a point $\ell$ of the projective line, a field $F_I$ that is an algebra over the residue field of $A$, a regular prolongation $R_g$ of $A$ from $\mathrm{fieldBar}\,q\,M'$ to $F_I$ (the same data as a constant reduction apart from the place map and divisor conditions) whose ring of integers is $\mathcal{O}^{\mathrm{Ig}}_\ell$, and a ring homomorphism $j$ from $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ to $F_I$ such that every $R_0$-integral $f$ has integral image in $R_g$ with $R_g$-residue equal to $j$ applied to its $R_0$-residue. Then for $s \in W$ and any two places $b_1, b_2$ of $F_I$ over the residue field of $A$ such that, for all $g$, $g$ lies in the valuation subring of $s$ if and only if $j(g)$ lies in the valuation subring of $b_i$ ($i = 1,2$), one has $b_1 = b_2$.
--
--   This is the uniqueness half of the statement that an Igusa component of the reduction of the level-$\Gamma_H(q^2M')$ modular curve meets the fibre over a supersingular point of the level-$M'$ curve in a single place, in the case $q = 3$; only uniqueness is asserted, existence of such a place being supplied separately. It feeds the assembly of the tube-annuli and node data for the semistable model at $q = 3$ in the case of divisible level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing_of_eq_three.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)

    (ℓ : CuspidalType.ProjLine q)
    {FI : Type} [Field FI] [Algebra (ResidueField A) FI]
    (Rg : RegularProlongation A (fieldBar q M') FI) (hRg : Rg.integers = OIg ℓ)
    (j : modularFunctionFieldC (ResidueField A) M' →+* FI)
    (hj : ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ Rg.integers,
        Rg.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩))
    (s : ↥W) (b₁ b₂ : Place (ResidueField A) FI)
    (hb₁ : ∀ g : modularFunctionFieldC (ResidueField A) M',
      g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔ j g ∈ b₁.toValuationSubring)
    (hb₂ : ∀ g : modularFunctionFieldC (ResidueField A) M',
      g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔ j g ∈ b₂.toValuationSubring) :
    b₁ = b₂ := by sorry
