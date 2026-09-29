-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_SemistableCovering_perPoint_w2Clauses_of_gaussPresentation_of_valuationSubring_over_fixed_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.SemistableCovering.perPoint_w2Clauses_of_gaussPresentation_of_valuationSubring_over_fixed_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/f19bbd21-3a1f-582a-a4f9-afcc6c1ce498
-- title:
--   Drinfeld and Igusa clauses of a semistable covering at q=2
-- statement:
--   Fix a prime $q$ together with the hypothesis $q=2$, a nonzero $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A)\,M'$ whose members are exactly the supersingular ones (rational, affine geometric, with value of the geometric $j$-generator in the supersingular $j$-set for $q$), and assume $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$, the latter being the function field over $\overline{\mathbb{Q}}$ of the modular curve $X_H$ of level $q^2M'$ with $H$ the kernel of $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$. Let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with residue target $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A)\,M'$, reducing Laurent series with coefficients in $A$ coefficientwise ($hR_0$), and let $\zeta$ be a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$. Given families of valuation subrings $O^{\mathrm{Ig}}$ of $\mathrm{fieldBar}\,q\,M'$ indexed by the projective line over $\mathbb{Z}/q$ and $O^{\mathrm{ss}}$ indexed by $W$, subject to: the Gauss presentation at $\mathrm{lineInfty}$ ($f \in O^{\mathrm{Ig}}_\infty$ iff $f\,y = x$ for Laurent series $x,y$ over $A$ with $y$ of nonzero reduction); each $O^{\mathrm{Ig}}_L$ is the pullback of $O^{\mathrm{Ig}}_\infty$ along a level automorphism $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ with $\gamma \in \Gamma_0(M')$ carrying $\mathrm{lineInfty}$ to $L$; injectivity of $L \mapsto O^{\mathrm{Ig}}_L$; permutation of this family by pullback along every $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma \in \Gamma_0(M')$; for $O^{\mathrm{ss}}_s$: it prolongs $A$, it lies over $s$ in the sense that every $R_0$-integral function whose divisor is nonnegative wherever the $j$-function is and whose reduction is $s$-integral lies in $O^{\mathrm{ss}}_s$ and is congruent modulo the maximal ideal to each $a \in A$ reducing to the value of that reduction at $s$, it is fixed by pullback along every level automorphism, and it contains an element $t$ with $t - a$ a unit for all $a \in A$; finally an element $\pi \in A$ with $\pi^{q^2-1} = q$, a ring homomorphism $\iota : \mathbb{F}_{q^2} \to \mathrm{ResidueField}\,A$, and a semistable covering $\mathcal{C}$ of type $\mathrm{SemistableCovering}\,q\,M'\,A\,W$ whose Igusa and supersingular chart integer rings are exactly $O^{\mathrm{Ig}}$ and $O^{\mathrm{ss}}$. Then, with $\mathrm{ResidueField}\,A$ an $\mathbb{F}_{q^2}$-algebra via $\iota$: first, for every primitive $q$-th root of unity $\zeta$ and every $s \in W$ there is $\eta \in \{1, q\}$ with $\mathcal{C}.\mathrm{DrinfeldClause}\,\pi\,\iota\,\eta\,\zeta\,s$, i.e. a subgroup $C$ of the $(q+1)$-st roots of unity of $\mathbb{F}_{q^2}$ and an isomorphism of the residue field of the chart at $s$ with the $C$-fixed subfield of the Drinfeld function field over $\mathrm{ResidueField}\,A$, intertwining the automorphisms induced on the chart by $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma^{-1}$ ($\gamma \in \Gamma_0(M')$) with the $H$-action of $\mathrm{redQ}\,q\,\gamma$ and those induced by inertia elements $\tau$ at $A$ with the $H$-action of $(\mathrm{diagOneElem}\,q\,(d^\eta)^{-1}, \alpha^\eta)$, where $\iota(\alpha)$ is the tame character value $A.\mathrm{tameCharacter}\,\pi\,\tau$ and $d \mapsto \alpha^{q+1}$; second, for every such $\zeta$, $\mathcal{C}.\mathrm{IgusaUnipotentClause}\,\zeta$: every $\gamma \in \Gamma_0(M')$ with unipotent reduction modulo $q$ acts through $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma^{-1}$ preserving the integers of the chart at $\mathrm{lineInfty}$ and inducing the identity on its residue field.
--
--   This is the verification, at $q = 2$ and with a rigidifying auxiliary prime $\ell \equiv 11 \pmod{12}$ dividing $M'$, of the two census clauses describing the special fibre of a semistable covering of the modular curve of level $q^2M'$: the supersingular components are Drinfeld (Igusa) curves with their $\Gamma_0(M')$- and inertia-equivariance, and the Igusa component at the cusp $\infty$ is fixed pointwise by unipotent level automorphisms. It is the form in which these clauses enter the assembly of a semistable covering with its equivalence clauses for a given family of valuation subrings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_SemistableCovering_perPoint_w2Clauses_of_gaussPresentation_of_valuationSubring_over_fixed_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.SemistableCovering.perPoint_w2Clauses_of_gaussPresentation_of_valuationSubring_over_fixed_of_eq_two_of_dvd
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
    (∀ (ζ : ModularCurve.FullLevel.Idx q) (s : ↥W), ∃ η : ℕ, (η = 1 ∨ η = q) ∧ 𝒞.DrinfeldClause π ι η ζ s) ∧
      (∀ ζ : ModularCurve.FullLevel.Idx q, 𝒞.IgusaUnipotentClause ζ) := by sorry
