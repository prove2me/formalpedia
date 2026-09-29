-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/a3b062c8-3df7-5e89-8aed-b5932cf87f0f
-- title:
--   Unique place of an Igusa component over a supersingular place, q=2
-- statement:
--   Fix a prime $q$ with $q = 2$, a nonzero level $M'$ with $q \nmid M'$, and a prime $\ell_0$ with $\ell_0 \equiv 11 \pmod{12}$ and $\ell_0 \mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$ (the predicate `LiesOverPrime`), and let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\kappa, M')$ over $\kappa = \mathrm{ResidueField}\,A$ whose members are exactly the supersingular places `ssPlaces q M' κ`, that is the rational places $w$ satisfying `IsAffineGeomPlace` whose value at `jGeomGen` lies in `ssJSet q`. Assume $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ inside the Laurent series over $\overline{\mathbb Q}$. Further data: a constant reduction $R_0$ of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}(\kappa, M')$ for which every Laurent series $y$ over $A$ whose coefficientwise image lies in $\mathrm{modularFunctionFieldBar}\,M'$ is $R_0$-integral with $R_0$-residue the coefficientwise reduction of $y$; a primitive $q$-th root of unity $\zeta$ (an element of `Idx q`); and valuation subrings $O^{Ig}_P$ of $\mathrm{fieldBar}\,q\,M'$ indexed by the points $P$ of $\mathbb P^1(\mathbb Z/q)$ such that $O^{Ig}_{\infty}$ consists of those $f$ for which there are Laurent series $x, y$ over $A$ with $y$ having nonzero coefficientwise reduction and $f \cdot y = x$ as Laurent series over $\overline{\mathbb Q}$, and such that every $P$ is of the form $\mathrm{redQ}\,q\,\gamma \cdot \infty$ for some $\gamma \in \Gamma_0(M')$ with $O^{Ig}_P$ the preimage of $O^{Ig}_{\infty}$ under $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$. Now fix a point $P$ of $\mathbb P^1(\mathbb Z/q)$, a field $F_I$ over $\kappa$, and a regular prolongation $R_g$ of $A$ from $\mathrm{fieldBar}\,q\,M'$ to $F_I$ whose ring of integers is $O^{Ig}_P$, together with a ring homomorphism $j : \mathrm{modularFunctionFieldC}(\kappa, M') \to F_I$ such that every $R_0$-integral $f$ is, via the inclusion of fields, $R_g$-integral with $R_g$-residue $j$ of its $R_0$-residue. Then for $s \in W$ and any two places $b_1, b_2$ of $F_I$ over $\kappa$ such that for all $g$ one has $g \in s$ iff $j(g) \in b_i$ ($i = 1, 2$), one has $b_1 = b_2$.
--
--   This expresses the total ramification of the Igusa covering above the supersingular points in characteristic $q$: an Igusa component has at most one place above a given supersingular place of the level-$M'$ modular curve over the residue field, read off through the map $j$ on reductions. It is the case $q = 2$ with the auxiliary rigidifying prime $\ell_0 \equiv 11 \pmod{12}$ dividing $M'$, and it feeds the construction of tube annuli, inertia data and node charts for the full-level semistable covering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing_of_eq_two_of_dvd
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
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
