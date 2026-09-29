-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/b543b714-e117-5de4-b90e-1aad450403ab
-- title:
--   Semistable covering of the full-level modular curve at q=3
-- statement:
--   Fix a prime $q$ with $q = 3$, a nonzero level $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$ (so $A$ lies over $q$), let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}$ over $\mathrm{ResidueField}\,A$ whose members are exactly the supersingular places `ssPlaces q M'`, assume $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant reduction of the level-$M'$ field along $A$ (a valuation subring of it prolonging $A$, with a surjective residue map onto $\mathrm{modularFunctionFieldC}$ whose kernel is the maximal ideal, compatible with degrees and divisors) which, by $h_{R_0}$, reduces Laurent series with coefficients in $A$ coefficientwise. Fix $\pi \in A$ with $\pi^{q^2-1} = q$, a ring homomorphism $\iota : \mathbb{F}_{q^2} \to \mathrm{ResidueField}\,A$, with $\mathrm{CoordRing}\,q\,(\mathrm{ResidueField}\,A)$ a domain, and an index $\zeta \in \mathrm{Idx}\,q$. Finally let $\mathcal{O}^{\mathrm{Ig}}$ assign a valuation subring of $\mathrm{fieldBar}\,q\,M'$ to each point of $\mathbb{P}^1(\mathbb{F}_q)$ and $\mathcal{O}^{\mathrm{ss}}$ one to each $s \in W$, subject to: $\mathcal{O}^{\mathrm{Ig}}(\infty)$ consists of the quotients $x/y$ of Laurent series with coefficients in $A$ for which the reduction of $y$ is nonzero; every other $\mathcal{O}^{\mathrm{Ig}}(\ell')$ is the pull-back of $\mathcal{O}^{\mathrm{Ig}}(\infty)$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for some $\gamma \in \Gamma_0(M')$ whose reduction moves $\infty$ to $\ell'$; $\mathcal{O}^{\mathrm{Ig}}$ is injective and each $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma \in \Gamma_0(M')$ permutes its values; each $\mathcal{O}^{\mathrm{ss}}(s)$ prolongs $A$, is fixed by all these level automorphisms, contains an element $t$ with $t - a$ a unit for every $a \in A$, and lies over the place $s$ in the sense that any $f$ in the integers of $R_0$ whose order is nonnegative wherever that of the $j$-function is, and whose $R_0$-reduction lies in the valuation subring of $s$, belongs to $\mathcal{O}^{\mathrm{ss}}(s)$, with $f - a$ in the maximal ideal whenever the residue of $a \in A$ is $s$-evaluation of that reduction. Given also fields $\mathrm{FSS}_0(s)$ over $\mathrm{ResidueField}\,A$, each a curve over it and essentially of finite type, with component charts whose integers are $\mathcal{O}^{\mathrm{ss}}(s)$, the conclusion asserts the existence of a semistable covering $\mathcal{C}$ of $\mathrm{fieldBar}\,q\,M'$ along $A$ indexed by $\mathbb{P}^1(\mathbb{F}_q)$ and $W$ (complete bipartite incidence, with annuli $\mathcal{C}.An$ joining the node $\mathcal{C}.xs$ on the $\ell'$-th Igusa chart to the node $\mathcal{C}.xt$ on the $s$-th supersingular chart), of a semistable model $M$ for the telescoped data $\mathcal{C}.\mathrm{sumFbar}$, $\mathcal{C}.\mathrm{sumChart}$, $\mathcal{C}.\mathrm{sumNode}$ — an integral, proper, flat scheme of locally finite presentation over $\mathrm{Spec}\,A$ realising the charts, places, annuli and nodes — and of a descent $D$ of $M$ to a Noetherian Henselian local subring, such that the charts carry exactly the prescribed rings ($(\mathcal{C}.CIg\,\ell').\mathrm{integers} = \mathcal{O}^{\mathrm{Ig}}(\ell')$ and $(\mathcal{C}.CSS\,s).\mathrm{integers} = \mathcal{O}^{\mathrm{ss}}(s)$) and all the head clauses hold: `EquivClauses` (equivariance of charts and annuli under the level automorphisms), for every $\zeta$ and $s$ a `DrinfeldClause` with exponent $\eta = 1$ or $\eta = q$ identifying the supersingular component with a Drinfeld quotient compatibly with the level and inertia actions, `IgusaUnipotentClause` for every $\zeta$, `LevelPinClauses` for $R_0$, `InertiaClause` and `WidthClause` for $\pi$, `GenusClause`, `DiscFibreClause`, `CurveClause`, `NaturalityClauses` and `InertiaIgusaInftyClause`.
--
--   This is the assembly step, in the case $q = 3$, producing the stable reduction of the full-level modular curve of level $q^2M'$ over a valuation ring above $q$: prescribed Igusa (Gauss) rings and charted supersingular rings are glued into a single semistable covering with a proper flat model over $A$ and a descent to a Henselian local base, carrying all the clauses needed later. The auxiliary rigid level $\ell \equiv 11 \pmod{12}$ dividing $M'$ guards against the extra automorphisms of the supersingular curve $j = 0 = 1728$ in characteristic $3$. It feeds the statement that packages the covering, model, descent and the per-point clauses at $q = 3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_three_of_dvd.lean

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

theorem ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_three_of_dvd
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
