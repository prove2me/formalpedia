-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted
-- name    : ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/c01ade6d-1f1f-5d09-84f6-26f4b83db3cb
-- title:
--   Assembly of the full-level semistable covering, model and descent
-- statement:
--   Let $q\ge 5$ be a prime, $M'\ge 1$ with $q\nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$; write $\kappa=\mathrm{ResidueField}\,A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ over $\kappa$ whose members are exactly the supersingular places $\mathrm{ssPlaces}\ q\ M'\ \kappa$, let $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\ q\ M'$ via `hle`, and let $R_0$ be a constant reduction of $A$ on $\mathrm{modularFunctionFieldBar}\,M'$ with values in $\mathrm{modularFunctionFieldC}\,\kappa\,M'$, pinned by `hR₀`: every Laurent series $y$ over $A$ whose coefficientwise image lies in $\mathrm{modularFunctionFieldBar}\,M'$ lies in $R_0.\mathrm{integers}$ and its $R_0$-residue is the coefficientwise residue of $y$. Let $\pi\in\overline{\mathbb Q}$ satisfy $\pi^{q^2-1}=q$ and $\pi\in A$, let $\iota:\mathbb F_{q^2}\to\kappa$ be a ring homomorphism, assume $\mathrm{CoordRing}\ q\ \kappa$ is a domain, and fix $\zeta\in\mathrm{Idx}\ q$. Given families of valuation subrings $O^{\mathrm{Ig}}_\ell\subseteq\mathrm{fieldBar}\ q\ M'$ for $\ell\in\mathbb P^1(\mathbb F_q)$ and $O^{\mathrm{ss}}_s$ for $s\in W$ such that: $O^{\mathrm{Ig}}_{\infty}$ consists of the $f$ expressible as a ratio $x/y$ of Laurent series with coefficients in $A$ whose denominator has nonzero coefficientwise residue; each $O^{\mathrm{Ig}}_\ell$ is the pull-back of $O^{\mathrm{Ig}}_{\infty}$ along $\mathrm{levelAutBar}\ q\ M'\ \zeta\ \gamma$ for some $\gamma\in\Gamma_0(M')$ with $\mathrm{redQ}\ q\ \gamma\cdot[1:0]=\ell$; $\ell\mapsto O^{\mathrm{Ig}}_\ell$ is injective; every $\mathrm{levelAutBar}\ q\ M'\ \zeta'\ \gamma$ with $\gamma\in\Gamma_0(M')$ permutes the $O^{\mathrm{Ig}}_\ell$; each $O^{\mathrm{ss}}_s$ prolongs $A$ (an element of $\overline{\mathbb Q}$ lies in $O^{\mathrm{ss}}_s$ exactly when it lies in $A$); each $O^{\mathrm{ss}}_s$ lies over $s$, in the sense that for $f\in R_0.\mathrm{integers}$ of nonnegative order at every place where the $j$-expansion $\mathrm{coeffEmb}\ \overline{\mathbb Q}\ \mathrm{jq}$ has nonnegative order and with $R_0$-residue in the valuation subring of $s$, the image of $f$ lies in $O^{\mathrm{ss}}_s$ and $f-a$ lies in the maximal ideal of $O^{\mathrm{ss}}_s$ for every $a\in A$ whose residue is $s.\mathrm{evalAt}$ of that $R_0$-residue; each $O^{\mathrm{ss}}_s$ is invariant under pull-back along all $\mathrm{levelAutBar}\ q\ M'\ \zeta'\ \gamma$, $\gamma\in\Gamma_0(M')$; and each $O^{\mathrm{ss}}_s$ contains an element $t$ with $t-a$ a unit of $O^{\mathrm{ss}}_s$ for all $a\in A$; and given, for each $s\in W$, a field $\mathrm{FSS}_0\,s$ that is a curve over $\kappa$ and essentially of finite type, together with a component chart $\mathrm{CSS}_0\,s$ for $(A,\mathrm{fieldBar}\ q\ M',\mathrm{FSS}_0\,s)$ whose ring of integers is $O^{\mathrm{ss}}_s$ — then, with $\kappa$ an $\mathbb F_{q^2}$-algebra via $\iota$, there exist a semistable covering $\mathcal C$ of type $\mathrm{SemistableCovering}\ q\ M'\ A\ W$, a semistable model $M$ over $A$ of $\mathrm{fieldBar}\ q\ M'$ whose vertex charts are $\mathcal C.\mathrm{sumChart}$, whose edges are indexed by $\mathbb P^1(\mathbb F_q)\times W$ with annuli $\mathcal C.\mathrm{An}\ \ell\ s$, source $\mathrm{inl}\,\ell$, target $\mathrm{inr}\,s$ and node places $\mathcal C.\mathrm{sumNode}$, and a descent datum $D$ for $M$, such that $(\mathcal C.\mathrm{CIg}\ \ell).\mathrm{integers}=O^{\mathrm{Ig}}_\ell$ and $(\mathcal C.\mathrm{CSS}\ s).\mathrm{integers}=O^{\mathrm{ss}}_s$, and $\mathcal C$ satisfies $\mathrm{EquivClauses}$ (equivariance of charts, domains, annulus domains and moduli under the level automorphisms, up to a permutation of $\mathbb P^1(\mathbb F_q)$), $\mathrm{W2Clauses}\ \pi\ \iota\ q$ (the Drinfeld clauses for all $\zeta',s$ and the Igusa unipotent clauses, with exponent parameter $q$), $\mathrm{LevelPinClauses}\ \mathrm{hle}\ R_0$, $\mathrm{InertiaClause}\ \pi$, $\mathrm{WidthClause}\ \langle\pi,\mathrm{h}\pi P\rangle$ (each annulus modulus is a unit times $\pi^w$ with $w\ge 1$), $\mathrm{GenusClause}$, $\mathrm{DiscFibreClause}$, $\mathrm{CurveClause}$, $\mathrm{NaturalityClauses}$ and $\mathrm{InertiaIgusaInftyClause}$.
--
--   This is the assembly step for the stable reduction of the full-level modular curve of level $q^2M'$ at the prime $q$: from the prescribed Igusa valuation rings indexed by $\mathbb P^1(\mathbb F_q)$ and the prescribed supersingular (Drinfeld) valuation rings indexed by the supersingular places of level $M'$, already presented by a chart, it produces a semistable covering of the function field along $A$ with complete bipartite incidence, a semistable model over $A$ realising it, a descent of that model to a Noetherian Henselian local subring, and all the clauses (equivariance, Drinfeld and Igusa census, level-$M'$ pins, tame inertia, widths, genus, disc fibres, curve-hood, naturality, inertia at the Igusa component over $[1:0]$) used further downstream. It is cited by [`ModularCurve.FullLevel.exists_semistableCovering_semistableModel_descent_equiv_w2_guards_inertiaInfty`](thm.html#ModularCurve.FullLevel.exists_semistableCovering_semistableModel_descent_equiv_w2_guards_inertiaInfty).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted.lean

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

open ModularCurve IsLocalRing CongruenceSubgroup
open AlgebraicCurve
open ModularCurve.FullLevel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted
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
      𝒞.EquivClauses ∧ 𝒞.W2Clauses π ι q ∧ 𝒞.LevelPinClauses hle R₀ ∧ 𝒞.InertiaClause π ∧
        𝒞.WidthClause ⟨π, hπP⟩ ∧ 𝒞.GenusClause ∧ 𝒞.DiscFibreClause ∧ 𝒞.CurveClause ∧ 𝒞.NaturalityClauses ∧
        𝒞.InertiaIgusaInftyClause := by sorry
