-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_eq_igusaRing_of_forall_mem_integers_mem_of_eq_two
-- name    : ModularCurve.FullLevel.exists_eq_igusaRing_of_forall_mem_integers_mem_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/8ce6660b-3fa5-5bce-8c8a-de2a5076182b
-- title:
--   Valuation rings over A containing R₀ are Igusa rings (q=2)
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'\ge 1$ with $q\nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$, in the sense that $q$ is a non-unit of $A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ over the residue field of $A$ whose members are exactly the supersingular places `ssPlaces q M'`, i.e. the rational affine geometric places at which the evaluation of `jGeomGen` lies in `ssJSet q`. Assume the base-changed level-$M'$ modular function field $\mathrm{modularFunctionFieldBar}\,M'$ is contained in $\mathrm{fieldBar}\,q\,M'$, the base change to $\overline{\mathbb Q}$ of the function field of $X_H$ at level $q^2M'$ with $H=$ `levelH q M'`. Let $R_0$ be a `ConstantReduction` of $A$ on $\mathrm{modularFunctionFieldBar}\,M'$ with residue field $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$: a valuation subring $R_0.\mathrm{integers}$ together with a surjective residue map onto that field whose kernel is the maximal ideal, inducing $A$ on constants, compatible with the residue map of $A$, with the usual norming and degree-preserving place map. Assume moreover that $R_0$ is coefficientwise reduction of $q$-expansions: every Laurent series $y$ with coefficients in $A$ whose image lies in $\mathrm{modularFunctionFieldBar}\,M'$ belongs to $R_0.\mathrm{integers}$, and its residue, read as a Laurent series over the residue field of $A$, is the coefficientwise reduction of $y$. Let $\zeta$ be a primitive $q$-th root of unity in $\overline{\mathbb Q}$, and let $\ell\mapsto \mathcal O^{\mathrm{Ig}}_\ell$ assign to each point of $\mathbb P^1(\mathbb Z/q)$ a valuation subring of $\mathrm{fieldBar}\,q\,M'$, such that at the point $[1:0]$ it is the Gauss ring consisting of those $f$ for which there are Laurent series $x,y$ with coefficients in $A$, the coefficientwise reduction of $y$ being non-zero, with $f\cdot y=x$, and such that for every $\ell$ there is $\gamma\in\Gamma_0(M')$ whose reduction modulo $q$ carries $[1:0]$ to $\ell$ and with $\mathcal O^{\mathrm{Ig}}_\ell$ the preimage of $\mathcal O^{\mathrm{Ig}}_{[1:0]}$ under the level automorphism $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$. Finally let $\mathcal O$ be a valuation subring of $\mathrm{fieldBar}\,q\,M'$ whose intersection with $\overline{\mathbb Q}$ is $A$, and which contains the image of $R_0.\mathrm{integers}$ under the inclusion of $\mathrm{modularFunctionFieldBar}\,M'$. Then $\mathcal O=\mathcal O^{\mathrm{Ig}}_\ell$ for some $\ell\in\mathbb P^1(\mathbb Z/q)$.
--
--   This identifies the prolongations to the full-level field of the good-reduction valuation of the level-$M'$ modular function field: any such valuation ring is one of the Igusa rings indexed by $\mathbb P^1(\mathbb F_q)$, here in the case $q=2$. It feeds the description of the Igusa components in the semistable covering of the full-level modular curve at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_eq_igusaRing_of_forall_mem_integers_mem_of_eq_two.lean

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

theorem ModularCurve.FullLevel.exists_eq_igusaRing_of_forall_mem_integers_mem_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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

    (O : ValuationSubring (fieldBar q M'))
    (hOA : ∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ O ↔ x ∈ A)
    (hOR₀ : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers →
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ O) :
    ∃ ℓ : CuspidalType.ProjLine q, O = OIg ℓ := by sorry
