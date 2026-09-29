-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/f605bab9-d5ac-5778-8b9f-772d9dc62f47
-- title:
--   Semistable covering, model and descent at q=2
-- statement:
--   Fix a prime $q$ with $q=2$, a nonzero level $M'$ with $q\nmid M'$, and a prime $\ell$ with $\ell\equiv 11\pmod{12}$ dividing $M'$; let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, and let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\kappa,M')$ over $\kappa=\mathrm{ResidueField}\,A$ whose members are exactly the supersingular places `ssPlaces q M' κ`. Assume $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'=:F$, and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with values in $\mathrm{modularFunctionFieldC}(\kappa,M')$ (a valuation subring with surjective residue map whose kernel is the maximal ideal, compatible with $A$ and with place degrees) such that the coefficientwise reduction of any Laurent series over $A$ lying in $\mathrm{modularFunctionFieldBar}\,M'$ is computed by $R_0$. Further data: $\pi\in\overline{\mathbb{Q}}$ with $\pi^{q^2-1}=q$ and $\pi\in A$; a ring map $\iota:\mathbb{F}_{q^2}\to\kappa$, with [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) a domain; an element $\zeta$ of $\mathrm{Idx}\,q$ (primitive $q$-th roots of unity in $\overline{\mathbb{Q}}$); and two families of valuation subrings of $F$, namely $O^{\mathrm{Ig}}$ indexed by $\mathbb{P}^1(\mathbb{Z}/q)$ and $O^{\mathrm{ss}}$ indexed by $W$. They are assumed to satisfy: $O^{\mathrm{Ig}}$ at the point $[1:0]$ is the set of $f\in F$ of the form $x/y$ with $x,y$ Laurent series over $A$ and $y$ of nonzero reduction; every $O^{\mathrm{Ig}}$ is the pullback of that one along some $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ with $\gamma\in\Gamma_0(M')$ whose reduction mod $q$ carries $[1:0]$ to the given point; $O^{\mathrm{Ig}}$ is injective; and each level automorphism permutes the family $O^{\mathrm{Ig}}$. On the other side, each $O^{\mathrm{ss}}_s$ prolongs $A$ ($\overline{\mathbb{Q}}$-elements lie in it exactly when they lie in $A$); it lies over $s$, in the sense that any $f$ in the integers of $R_0$ which is regular at every place where the image of $j$ is regular and whose $R_0$-residue lies in the valuation subring of $s$ belongs to $O^{\mathrm{ss}}_s$, and $f-a$ lies in the maximal ideal of $O^{\mathrm{ss}}_s$ whenever $a\in A$ reduces to $s$-evaluation of the residue of $f$; $O^{\mathrm{ss}}_s$ is fixed by the pullback of every $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$, $\gamma\in\Gamma_0(M')$; and it contains an element $t$ with $t-a$ a unit for all $a\in A$. Finally, fields $F^{\mathrm{ss}}_{0,s}$ over $\kappa$, each a curve over $\kappa$ of essentially finite type, are given together with component charts $C^{\mathrm{ss}}_{0,s}$ of $F$ along $A$ whose integers are $O^{\mathrm{ss}}_s$. Then, with $\kappa$ an $\mathbb{F}_{q^2}$-algebra via $\iota$, there exist a semistable covering $\mathcal{C}$ of $F$ along $A$ indexed by $\mathbb{P}^1(\mathbb{Z}/q)$ and $W$, a semistable model $M$ over $A$ of $F$ for the combined chart family $\mathcal{C}.\mathrm{sumChart}$ with annuli $\mathcal{C}.\mathrm{An}\,\ell\,s$ indexed by $\mathbb{P}^1(\mathbb{Z}/q)\times W$ joining the Igusa component $\ell$ to the supersingular component $s$ at the node places $\mathcal{C}.\mathrm{sumNode}$, and a descent datum $D$ for $M$ (a Noetherian henselian local subring $A_0$ of $A$ with an algebraic subfield of definition and a model over $A_0$ pulling back to $M$), such that the Igusa charts of $\mathcal{C}$ have integers $O^{\mathrm{Ig}}_\ell$, its supersingular charts have integers $O^{\mathrm{ss}}_s$, and all of the following hold: the equivariance clauses $\mathcal{C}.\mathrm{EquivClauses}$ (each level automorphism $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$, $\gamma\in\Gamma_0(M')$, permutes the Igusa charts' integers and domains, fixes those of the supersingular charts, and matches annulus domains and moduli); for every $\zeta$ and every $s\in W$ some exponent $\eta\in\{1,q\}$ with the Drinfeld clause $\mathcal{C}.\mathrm{DrinfeldClause}\,\pi\,\iota\,\eta\,\zeta\,s$, identifying the reduced field at $s$ with a quotient field of the Drinfeld curve by a subgroup of the $(q+1)$-st roots of unity compatibly with the $\Gamma_0(M')$-action and with tame inertia through the tame character $\pi$-normalised and raised to the power $\eta$; for every $\zeta$ the Igusa unipotent clause (level automorphisms with unipotent reduction induce the identity on the chart at $[1:0]$); the level pinning clauses for $hle$ and $R_0$; the inertia clause for $\pi$ (inertia elements with trivial tame character induce the identity on all charts, fix place maps, domains and annulus parameters); the width clause for $\pi\in A$ (every annulus modulus is a unit times $\pi^{w}$ with $w\ge 1$); the genus clause (the genus of $F$ plus the number of components equals the sum of the genera of the reduced fields plus the number of nodes plus one); the disc-fibre clause; the curve clause (each reduced field is a curve of essentially finite type over $\kappa$); the naturality clauses; and the clause governing inertia on the Igusa chart at $[1:0]$.
--
--   This is the assembly step for the stable reduction of the full-level modular curve at the prime $q=2$ with rigidifying auxiliary level $\ell\equiv 11\pmod{12}$: from the given Igusa and Drinfeld valuation subrings of the full-level function field it produces the complete bipartite semistable covering together with a semistable model over $A$ and a descent of that model to a Noetherian henselian local subring, and verifies all the clauses (equivariance, Drinfeld identification, level pinning, inertia, widths, genus, disc fibres, curve-hood, naturality) used downstream. It is cited by the corresponding existence statement packaging covering, model, descent and the per-point clauses at $q=2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_two_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringInertiaIgusa

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open AlgebraicCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_two_of_dvd
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
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField A)
    [IsDomain (DrinfeldCurve.CoordRing q (IsLocalRing.ResidueField A))]
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

    (FSS₀ : ↥W → Type) [∀ s, Field (FSS₀ s)] [∀ s, Algebra (ResidueField A) (FSS₀ s)]
    [∀ s, IsCurveOver (ResidueField A) (FSS₀ s)] [∀ s, Algebra.EssFiniteType (ResidueField A) (FSS₀ s)]
    (CSS₀ : ∀ s, ComponentChart A (fieldBar q M') (FSS₀ s)) (hCSS₀ : ∀ s, (CSS₀ s).integers = OSS s) :
    letI : Algebra (GaloisField q 2) (IsLocalRing.ResidueField A) := ι.toAlgebra
    ∃ 𝒞 : SemistableCovering q M' A W,
      ∃ (M : AlgebraicCurve.SemistableModel A ↥(ModularCurve.FullLevel.fieldBar q M') 𝒞.sumFbar 𝒞.sumChart
          (fun e : CuspidalType.ProjLine q × ↥W => 𝒞.An e.1 e.2)
          (fun e => Sum.inl e.1) (fun e => Sum.inr e.2)
          (fun e => 𝒞.sumNode (Sum.inl e.1) e) (fun e => 𝒞.sumNode (Sum.inr e.2) e))
        (D : M.Descent),
      (∀ ℓ, (𝒞.CIg ℓ).integers = OIg ℓ) ∧ (∀ s, (𝒞.CSS s).integers = OSS s) ∧
      𝒞.EquivClauses ∧
      (∀ (ζ : ModularCurve.FullLevel.Idx q) (s : ↥W), ∃ η : ℕ, (η = 1 ∨ η = q) ∧ 𝒞.DrinfeldClause π ι η ζ s) ∧
      (∀ ζ : ModularCurve.FullLevel.Idx q, 𝒞.IgusaUnipotentClause ζ) ∧ 𝒞.LevelPinClauses hle R₀ ∧ 𝒞.InertiaClause π ∧
        𝒞.WidthClause ⟨π, hπP⟩ ∧ 𝒞.GenusClause ∧ 𝒞.DiscFibreClause ∧ 𝒞.CurveClause ∧ 𝒞.NaturalityClauses ∧
        𝒞.InertiaIgusaInftyClause := by sorry
