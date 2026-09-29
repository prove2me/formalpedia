-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_SemistableCovering_w2Clauses_of_gaussPresentation_of_valuationSubring_over_fixed
-- name    : ModularCurve.FullLevel.SemistableCovering.w2Clauses_of_gaussPresentation_of_valuationSubring_over_fixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/3aac97ff-9eed-546f-8691-7c325363defa
-- title:
--   W2 clauses of a semistable covering from its chart rings
-- statement:
--   Fix a prime $q\ge 5$ and a nonzero level $M'$ with $q\nmid M'$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, and a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ over the residue field of $A$ whose members are exactly the supersingular places (rational, affine geometric, with $j$-value in the supersingular set). Assume $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant reduction of the base-changed full level-$M'$ modular function field along $A$ onto $\mathrm{modularFunctionFieldC}$, compatible with coefficientwise reduction of Laurent series with coefficients in $A$ ($hR_0$). Let $\zeta$ be a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$, and let $O^{\mathrm{Ig}}$, indexed by the projective line over $\mathbb{Z}/q$, and $O^{\mathrm{ss}}$, indexed by $W$, be families of valuation subrings of $\mathrm{fieldBar}\,q\,M'$. The Igusa hypotheses are: the Gauss presentation $f\in O^{\mathrm{Ig}}(\infty)$ iff $f\,y=x$ for Laurent series $x,y$ over $A$ with $y$ having nonzero reduction; each $O^{\mathrm{Ig}}(\ell)$ is the pullback of $O^{\mathrm{Ig}}(\infty)$ along a level automorphism $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ with $\gamma\in\Gamma_0(M')$ carrying $\infty$ to $\ell$; injectivity of $\ell\mapsto O^{\mathrm{Ig}}(\ell)$; and permutation of the family by all pullbacks along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$, $\gamma\in\Gamma_0(M')$. The supersingular hypotheses are: $O^{\mathrm{ss}}(s)$ meets the constants exactly in $A$; every $f$ in the integers of $R_0$ which is regular wherever the base-changed $j$ is regular and whose $R_0$-reduction lies in the valuation ring of $s$ lies in $O^{\mathrm{ss}}(s)$, and $f-a$ lies in the maximal ideal of $O^{\mathrm{ss}}(s)$ for every $a\in A$ whose residue is the value at $s$ of that reduction; each $O^{\mathrm{ss}}(s)$ is fixed by every pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma\in\Gamma_0(M')$; and each $O^{\mathrm{ss}}(s)$ contains an element $t$ with $t-a$ a unit for all $a\in A$. Finally let $\pi\in A$ satisfy $\pi^{q^2-1}=q$, let $\iota:\mathbb{F}_{q^2}\to\mathrm{ResidueField}\,A$ be a ring homomorphism with the Drinfeld coordinate ring over the residue field a domain, and let $\mathcal{C}$ be a semistable covering for $(q,M',A,W)$ whose Igusa and supersingular chart rings are exactly $O^{\mathrm{Ig}}$ and $O^{\mathrm{ss}}$. Then, with the $\mathbb{F}_{q^2}$-algebra structure on the residue field given by $\iota$, $\mathcal{C}$ satisfies $\mathcal{C}.\mathrm{W2Clauses}\,\pi\,\iota\,q$: the Drinfeld clause with exponent $\eta=q$ for every $\zeta'$ and every $s\in W$, and the Igusa unipotent clause for every $\zeta'$.
--
--   This is the step that verifies, for a semistable covering of the full level-$q^2M'$ modular curve along a place of $\overline{\mathbb{Q}}$ above $q$, the two structural clauses describing its components: the supersingular components are Drinfeld (Deligne–Lusztig) curves with the prescribed level and inertia actions, and the Igusa component at $\infty$ is fixed pointwise by the unipotent part of the level structure. It is invoked by the assembly producing a semistable covering together with its clauses from given valuation subrings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_SemistableCovering_w2Clauses_of_gaussPresentation_of_valuationSubring_over_fixed.lean

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

theorem ModularCurve.FullLevel.SemistableCovering.w2Clauses_of_gaussPresentation_of_valuationSubring_over_fixed
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
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

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
    (hCIg : ∀ ℓ, (𝒞.CIg ℓ).integers = OIg ℓ) (hCSS : ∀ s, (𝒞.CSS s).integers = OSS s) :
    letI : Algebra (GaloisField q 2) (IsLocalRing.ResidueField A) := ι.toAlgebra
    𝒞.W2Clauses π ι q := by sorry
