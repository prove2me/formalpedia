-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing
-- name    : ModularCurve.FullLevel.eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/7dc16c73-efb1-5d2d-8091-46cf6e8f2ff9
-- title:
--   Uniqueness of the place over a supersingular place
-- statement:
--   Fix a prime $q\ge 5$ and a non-zero natural number $M'$ with $q\nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$, in the sense that $q$ is a non-unit of $A$; write $\kappa$ for its residue field. Let $W$ be a finite set of places of `modularFunctionFieldC` $\kappa\,M'$ over $\kappa$ whose members are exactly the supersingular places `ssPlaces q M' κ`, that is the rational affine geometric places whose value at the $j$-generator lies in the supersingular $j$-set. Assume `modularFunctionFieldBar M'` $\le$ `fieldBar q M'` inside the Laurent series over $\overline{\mathbb Q}$. Let $R_0$ be a `ConstantReduction` of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC` $\kappa\,M'$ such that every Laurent series $y$ with coefficients in $A$ whose image in the Laurent series over $\overline{\mathbb Q}$ lies in `modularFunctionFieldBar M'` is $R_0$-integral, with $R_0$-residue equal, as a Laurent series over $\kappa$, to the coefficientwise reduction of $y$. Let $\zeta$ be a primitive $q$-th root of unity in $\overline{\mathbb Q}$, and let $\mathcal O^{\mathrm{Ig}}$ assign a valuation subring of `fieldBar q M'` to each point of $\mathbb P^1(\mathbb F_q)$, subject to: membership of $f$ in $\mathcal O^{\mathrm{Ig}}(\infty)$ holds precisely when there are Laurent series $x,y$ with coefficients in $A$, the coefficientwise reduction of $y$ non-zero, with $f\cdot y=x$; and for each $\ell$ there is $\gamma\in\Gamma_0(M')$ whose reduction mod $q$ carries $\infty$ to $\ell$ and with $\mathcal O^{\mathrm{Ig}}(\ell)$ the preimage of $\mathcal O^{\mathrm{Ig}}(\infty)$ under `levelAutBar q M' ζ γ`. Fix $\ell$, a field $F_I$ over $\kappa$, and a `RegularProlongation` $R_g$ of $A$ from `fieldBar q M'` to $F_I$ whose ring of integers is $\mathcal O^{\mathrm{Ig}}(\ell)$, together with a ring homomorphism $j$ from `modularFunctionFieldC` $\kappa\,M'$ to $F_I$ such that every $R_0$-integral $f$ has $R_g$-integral image in `fieldBar q M'` with $R_g$-residue $j$ of the $R_0$-residue of $f$. Then for $s\in W$ and places $b_1,b_2$ of $F_I$ over $\kappa$ such that, for all $g$, $g$ lies in the valuation subring of $s$ exactly when $j(g)$ lies in that of $b_i$ ($i=1,2$), one has $b_1=b_2$. Only this uniqueness is asserted; no place above $s$ is produced.
--
--   This is the uniqueness half of the total ramification of the Igusa covering above the supersingular points of $X_0(M')$ in characteristic $q$, transported to an abstract reduced field $F_I$ along the identification of the Igusa ring $\mathcal O^{\mathrm{Ig}}(\ell)$ with a translated Gauss ring and of $j$ with an inclusion of function fields. It feeds the construction of tube annuli, discs, node rings and charts for the semistable covering of the full-level modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve IsLocalRing CongruenceSubgroup
open ModularCurve.FullLevel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
