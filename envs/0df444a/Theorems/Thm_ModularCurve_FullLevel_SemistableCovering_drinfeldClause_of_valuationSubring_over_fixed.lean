-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_SemistableCovering_drinfeldClause_of_valuationSubring_over_fixed
-- name    : ModularCurve.FullLevel.SemistableCovering.drinfeldClause_of_valuationSubring_over_fixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/e305849d-c1f7-5cb4-ab5f-6bea6d396208
-- title:
--   Drinfeld clause for supersingular charts from their valuation rings
-- statement:
--   Let $q\ge 5$ be a prime, $M'$ a nonzero natural number with $q\nmid M'$, and $A$ a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$; write $\kappa=\mathrm{ResidueField}\,A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ over $\kappa$ consisting exactly of the supersingular places `ssPlaces q M' κ` (rational affine geometric places whose value at the geometric $j$-generator lies in `ssJSet q κ`). Assume $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$ inside the Laurent series over $\overline{\mathbb{Q}}$, and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with values in $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ which, by hypothesis, reduces every $q$-expansion with coefficients in $A$ coefficientwise. For each $s\in W$ let $\mathcal{O}_s$ be a valuation subring of $\mathrm{fieldBar}\,q\,M'$ such that: $\mathcal{O}_s$ pulls back to $A$ on $\overline{\mathbb{Q}}$; every $f\in R_0.\mathrm{integers}$ that is regular wherever the image of $j$ is regular and whose $R_0$-residue lies in the valuation ring of $s$ lies in $\mathcal{O}_s$, with $f-a$ in the maximal ideal of $\mathcal{O}_s$ for each $a\in A$ whose residue is the value of that residue at $s$; $\mathcal{O}_s$ is stable under the comap of $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ for every $\zeta'\in\mathrm{Idx}\,q$ and every $\gamma\in\Gamma_0(M')$; and $\mathcal{O}_s$ contains an element $t$ such that $t-a$ is a unit of $\mathcal{O}_s$ for all $a\in A$. Let $\pi\in A$ satisfy $\pi^{q^2-1}=q$, let $\iota:\mathbb{F}_{q^2}\to\kappa$ be a ring homomorphism making $\mathrm{CoordRing}\,q\,\kappa$ a domain, and let $\mathcal{C}$ be a semistable covering for $q,M',A,W$ whose supersingular chart at each $s$ has $(\mathcal{C}.\mathrm{CSS}\,s).\mathrm{integers}=\mathcal{O}_s$. Then, with $\kappa$ an $\mathbb{F}_{q^2}$-algebra via $\iota$, for every $\zeta\in\mathrm{Idx}\,q$ and every $s\in W$ the predicate $\mathcal{C}.\mathrm{DrinfeldClause}\,\pi\,\iota\,q\,\zeta\,s$ holds: there are a subgroup $C\le\mu_{q+1}(\mathbb{F}_{q^2})$ and a $\kappa$-algebra isomorphism $e$ from $\mathcal{C}.\mathrm{FSS}\,s$ onto the $C$-fixed subfield of the Drinfeld function field $\mathrm{Frac}(\mathrm{CoordRing}\,q\,\kappa)$ such that, for each $\gamma\in\Gamma_0(M')$, some ring automorphism of $\mathcal{C}.\mathrm{FSS}\,s$ is induced on the chart $\mathcal{C}.\mathrm{CSS}\,s$ by $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma^{-1}$ and every such automorphism transports under $e$ to the $\mathrm{hSubgroup}$-action of $(\gamma\bmod q,1)$, and, for each $\tau$ in the inertia subgroup of $A$ over $\mathbb{Q}$ and each $\alpha\in\mathbb{F}_{q^2}^{\times}$ with $\iota(\alpha)=A.\mathrm{tameCharacter}\,\pi\,\tau$, some automorphism is induced on the chart by the arithmetic Galois action of $\tau$ and every such automorphism transports under $e$ to the action of $(\mathrm{diagOneElem}\,q\,(d^{q})^{-1},\alpha^{q})$ for any $d\in(\mathbb{Z}/q)^{\times}$ mapping to $\alpha^{q+1}$.
--
--   This is the supersingular half of the structural ("W2") description of a semistable covering of the full-level modular curve: the level-fixed valuation rings $\mathcal{O}_s$ lying over the supersingular points are pinned to the Gauss valuations of the Drinfeld components, and the reduced chart fields are identified, equivariantly for $\Gamma_0(M')$ and for tame inertia, with fixed fields of the Drinfeld curve $xy^q-x^qy=1$ over $\kappa$. It feeds the assembly of the full set of W2 clauses and the compatibility of inertia with the supersingular discs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_SemistableCovering_drinfeldClause_of_valuationSubring_over_fixed.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.SemistableCovering.drinfeldClause_of_valuationSubring_over_fixed
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
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField A)
    [IsDomain (DrinfeldCurve.CoordRing q (IsLocalRing.ResidueField A))]
    (𝒞 : SemistableCovering q M' A W)
    (hCSS : ∀ s, (𝒞.CSS s).integers = OSS s) :
    letI : Algebra (GaloisField q 2) (IsLocalRing.ResidueField A) := ι.toAlgebra
    ∀ (ζ : Idx q) (s : ↥W), 𝒞.DrinfeldClause π ι q ζ s := by sorry
