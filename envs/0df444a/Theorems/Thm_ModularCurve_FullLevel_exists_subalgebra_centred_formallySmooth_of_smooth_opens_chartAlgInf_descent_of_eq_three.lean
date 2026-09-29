-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgInf_descent_of_eq_three
-- name    : ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgInf_descent_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/5bac2799-68fe-5766-ae0c-8e7b6972a508
-- title:
--   Centred formally smooth subalgebra on the pole chart, q=3
-- statement:
--   Throughout, $q$ is a prime with $q=3$ and $M'$ is a nonzero natural number not divisible by $q$; $A$ is a valuation subring of $\overline{\mathbb Q}$ lying over $q$ in the sense that $q$ is a non-unit of $A$ (`LiesOverPrime`). The finite set $W$ consists, by `hW`, of exactly the places $w$ of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$ over the residue field of $A$ belonging to `ssPlaces q M'`, i.e. those $w$ that are rational (the structure map of the residue field of $A$ into the residue field of $w$ is surjective), satisfy the predicate `IsAffineGeomPlace`, and whose value `w.evalAt (jGeomGen _ M')` lies in `ssJSet q`. The hypothesis `hle` records the inclusion of intermediate fields $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$ inside $\mathrm{LaurentSeries}(\overline{\mathbb Q})$, the first being the base change to $\overline{\mathbb Q}$ of the full level-$M'$ modular function field, the second the geometric $\Gamma_H(q^2M')$-field for $H=\mathrm{levelH}\,q\,M'$.
--
--   Reduction data: $R_0$ is a `ConstantReduction` of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A,M')$, that is, a valuation subring `R₀.integers` together with a surjective residue homomorphism onto the target whose kernel is the maximal ideal, inducing $A$ on constants and compatible with the residue map of $A$, satisfying the scaling clause `exists_smul_mem`, and carrying a degree-preserving map on places compatible with orders of functions. The hypothesis `hR₀` says that for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb Q}$ lies in $\mathrm{modularFunctionFieldBar}\,M'$, that element lies in `R₀.integers` and its $R_0$-residue, read as a Laurent series over the residue field of $A$, is the coefficientwise reduction of $y$. Further, $\pi\in A$ satisfies $\pi^{q^2-1}=q$, and $\zeta$ is a primitive $q$-th root of unity in $\overline{\mathbb Q}$ (an element of `Idx q`).
--
--   Two families of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ are given: $\mathcal O_{\mathrm{Ig}}=\mathrm{OIg}$ indexed by $\mathbb P^1(\mathbb F_q)=$ [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21), and $\mathcal O_{\mathrm{ss}}=\mathrm{OSS}$ indexed by $W$. The Igusa group of hypotheses consists of: `hIg_inf`, which describes $\mathcal O_{\mathrm{Ig}}(\infty)$ as the set of $f$ admitting Laurent series $x,y$ over $A$ with $y$ of nonzero coefficientwise reduction and $f\cdot y=x$ after pushing coefficients into $\overline{\mathbb Q}$; `hIg`, which for each $\ell$ produces $\gamma\in\Gamma_0(M')$ with $\mathrm{redQ}\,q\,\gamma\cdot\infty=\ell$ and $\mathcal O_{\mathrm{Ig}}(\ell)$ the pullback of $\mathcal O_{\mathrm{Ig}}(\infty)$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$; `hIg_inj`, injectivity of $\ell\mapsto\mathcal O_{\mathrm{Ig}}(\ell)$; and `hIg_perm`, which says that pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ for $\gamma\in\Gamma_0(M')$ permutes the family. The supersingular group consists of: `hSS_A`, that a constant from $\overline{\mathbb Q}$ lies in $\mathcal O_{\mathrm{ss}}(s)$ precisely when it lies in $A$; `hSS_over`, which for $s\in W$ and $f$ in `R₀.integers` whose order is non-negative at every place of $\mathrm{modularFunctionFieldBar}\,M'$ at which $\hat\jmath=\mathrm{coeffEmb}\,\overline{\mathbb Q}\,jq$ has non-negative order, and whose $R_0$-residue lies in the valuation subring of $s$, asserts that the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $\mathcal O_{\mathrm{ss}}(s)$ and that for every $a\in A$ whose residue equals the value at $s$ of the $R_0$-residue of $f$, the difference of that image and $a$ lies in the maximal ideal of $\mathcal O_{\mathrm{ss}}(s)$; `hSS_fix`, invariance of each $\mathcal O_{\mathrm{ss}}(s)$ under pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ for $\gamma\in\Gamma_0(M')$; and `hSS_tr`, which provides for each $s\in W$ an element $t\in\mathcal O_{\mathrm{ss}}(s)$ such that $t-a$ is a unit of $\mathcal O_{\mathrm{ss}}(s)$ for every $a\in A$.
--
--   Descent data: $K_0$ is a subfield of $\overline{\mathbb Q}$ with $\overline{\mathbb Q}$ algebraic over it and $\pi\in K_0$; $A_0$ is a henselian discrete valuation domain with an injective local ring homomorphism $\iota:A_0\to A$ whose image in $\overline{\mathbb Q}$ is exactly $A\cap K_0$ (`hιK₀`) and such that the residue map of $A$ composed with $\iota$ is surjective (`hres`); $\varpi_0$ generates the maximal ideal of $A_0$ and $\iota(\varpi_0)=\pi$ in $\overline{\mathbb Q}$. The subfield $F_0$ of $\mathrm{fieldBar}\,q\,M'$ is characterised by `hF₀` as the set of elements all of whose Laurent coefficients lie in $K_0$; by `hjF₀` the image of $\hat\jmath$ lies in $F_0$, and $\hat\jmath_0$ denotes the corresponding nonzero element of $F_0$. An $A_0$-algebra structure on $F_0$ is given, compatible with $\iota$ in the sense of `hj₀`.
--
--   Chart and centre data: $V$ is a valuation subring of $F_0$ contained in the preimage of $\mathcal O_{\mathrm{Ig}}(\infty)$ (`hV`) and strictly so, since by `hVlt` some element of $F_0$ lies in $\mathcal O_{\mathrm{Ig}}(\infty)$ but not in $V$. The pole chart $C=\mathrm{chartAlgInf}\,A_0\,F_0\,\hat\jmath_0$, the $A_0$-subalgebra of elements of $F_0$ integral over $A_0[\hat\jmath_0^{-1}]$, is contained in $V$ (`hCV`), and $\mathfrak n$ is a maximal ideal of $C$ consisting exactly of the elements of $C$ that are non-units of $V$ (`h𝔫`), i.e. the centre of $V$ on the chart. The hypothesis `hnotSS` says that for every $s\in W$ either some element of $C$ lies in the maximal ideal of $\mathcal O_{\mathrm{ss}}(s)$ without lying in $\mathfrak n$, or some element of $C$ fails to lie in $\mathcal O_{\mathrm{ss}}(s)$. The family $\mathfrak q:\mathbb P^1(\mathbb F_q)\to\mathrm{Ideals}(C)$ satisfies: `hLOC`, that for each $\ell$ the elements of $F_0$ landing in $\mathcal O_{\mathrm{Ig}}(\ell)$ are exactly the fractions $b/c$ with $b,c\in C$, $c\notin\mathfrak q(\ell)$; `hMIN`, that each $\mathfrak q(\ell)$ is a minimal prime over the ideal of $C$ generated by the image of the maximal ideal of $A_0$; `hINJ`, injectivity of $\mathfrak q$; and `hSURJ`, that every minimal prime over that ideal is of the form $\mathfrak q(\ell)$. The hypothesis `hGENFIB` says that every nonzero prime $\mathfrak p$ of $C$ not containing the image of $\varpi_0$ has the property that the fractions $b/c$ with $b,c\in C$ and $c\notin\mathfrak p$ form a valuation subring of $F_0$. Finally $U$ is an open subscheme of the two-chart integral model $\mathrm{TwoChartIntegralModel}\,A_0\,F_0\,\hat\jmath_0$ (the pushout gluing the spectra of the finite and pole charts along the middle chart), the image of the point $\mathfrak n$ under the canonical morphism `ιInf` from the spectrum of the pole chart lies in $U$ (`hxU`), and the inclusion $U\hookrightarrow \mathrm{TwoChartIntegralModel}$ followed by the structure morphism `toBase` to $\operatorname{Spec} A_0$ is smooth (`hU`).
--
--   Under these hypotheses there exist an $A_0$-subalgebra $B$ of $F_0$ and a maximal ideal $\mathfrak m$ of $B$ such that all of the following hold. First, $B$ is finitely generated as an $A_0$-algebra. Second, $B$ is integrally closed in $F_0$: every $x\in F_0$ integral over $B$ lies in $B$. Third, $F_0$ is the field of fractions of $B$: every $x\in F_0$ can be written as $x=b/c$ with $b,c\in B$, $c\neq 0$. Fourth, every prime $\mathfrak q$ of $B$ that contains the image in $B$ of the maximal ideal of $A_0$ and is not maximal is a minimal prime over that image ideal. Fifth, for every nonzero prime $\mathfrak p$ of $B$ not containing that image ideal, the set of $f\in F_0$ of the form $f=b/c$ with $b,c\in B$, $c\notin\mathfrak p$, is a valuation subring of $F_0$. Sixth, if every element of $B$ maps into $\mathcal O_{\mathrm{Ig}}(\ell')$ then $\ell'=\infty$, i.e. $\mathcal O_{\mathrm{Ig}}(\infty)$ is the only Igusa ring containing $B$. Seventh, for no $s\in W$ does all of $B$ map into $\mathcal O_{\mathrm{ss}}(s)$. Eighth, there is a prime $\mathfrak q$ of $B$ such that an $x\in F_0$ lies in $\mathcal O_{\mathrm{Ig}}(\infty)$ precisely when $x=b/c$ with $b,c\in B$ and $c\notin\mathfrak q$. Ninth, every minimal prime $\mathfrak q$ over the image in $B$ of the maximal ideal of $A_0$ has this same property: $x\in F_0$ lies in $\mathcal O_{\mathrm{Ig}}(\infty)$ iff $x=b/c$ with $b,c\in B$, $c\notin\mathfrak q$. Tenth, $B\subseteq V$ and $\mathfrak m$ consists exactly of the elements of $B$ that are non-units of $V$, so $\mathfrak m$ is the centre of $V$ on $B$. Eleventh, $\hat\jmath_0\in B$ or $\hat\jmath_0^{-1}\in B$. Twelfth, the structure map from $A_0$ to the localisation of $B$ at $\mathfrak m$ is formally smooth.
--
--   This is the $q=3$ instance of the construction of the "good" package in the dichotomy for the Igusa charts of the descended two-chart model: at a centre on the pole chart which lies in a smooth open of the model and is not a supersingular centre, a finitely generated, integrally closed, centred $A_0$-subalgebra of $F_0$ is produced whose localisation at the centre is formally smooth over $A_0$ and whose Igusa and supersingular separation properties are those required downstream. It is used by [`ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent_of_eq_three`](thm.html#ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent_of_eq_three) in the construction of the semistable covering of the full-level modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgInf_descent_of_eq_three.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgInf_descent_of_eq_three
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
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
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

    (K₀ : Subfield (AlgebraicClosure ℚ)) [Algebra.IsAlgebraic ↥K₀ (AlgebraicClosure ℚ)] (hπK₀ : π ∈ K₀)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hιK₀ : Set.range (fun a : A₀ => ((ι a : ↥A) : AlgebraicClosure ℚ)) =
      (A : Set (AlgebraicClosure ℚ)) ∩ (K₀ : Set (AlgebraicClosure ℚ)))
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})

    (hϖ₀π : ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) = π)

    (F₀ : Subfield ↥(fieldBar q M'))
    (hF₀ : ∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K₀)

    (hjF₀ : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)

    [Algebra A₀ ↥F₀]
    (hj₀ : ∀ a : A₀, ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ))
    [Fact ((⟨_, hjF₀⟩ : ↥F₀) ≠ 0)]
    (V : ValuationSubring ↥F₀)
    (hV : ∀ f : ↥F₀, f ∈ V → (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q))
    (hVlt : ∃ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ∧ f ∉ V)
    (hCV : ∀ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), (g : ↥F₀) ∈ V)
    (𝔫 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (h𝔫max : 𝔫.IsMaximal)
    (h𝔫 : ∀ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), g ∈ 𝔫 ↔ (g : ↥F₀) ∈ V.nonunits)

    (hnotSS : ∀ s : ↥W, (∃ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
        (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) ∧ g ∉ 𝔫) ∨
      (∃ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), ((g : ↥F₀) : ↥(fieldBar q M')) ∉ OSS s))

    (𝔮 : CuspidalType.ProjLine q → Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)))
    (hLOC : ∀ ℓ (x : ↥F₀), (x : ↥(fieldBar q M')) ∈ OIg ℓ ↔
      ∃ b c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), c ∉ 𝔮 ℓ ∧ x * (c : ↥F₀) = (b : ↥F₀))
    (hMIN : ∀ ℓ, 𝔮 ℓ ∈ (Ideal.map (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (maximalIdeal A₀)).minimalPrimes)
    (hINJ : Function.Injective 𝔮)
    (hSURJ : ∀ 𝔮' : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      𝔮' ∈ (Ideal.map (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (maximalIdeal A₀)).minimalPrimes → ∃ ℓ, 𝔮' = 𝔮 ℓ)

    (hGENFIB : ∀ 𝔭 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), 𝔭.IsPrime → 𝔭 ≠ ⊥ → algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀ ∉ 𝔭 →
      ∃ V₁ : ValuationSubring ↥F₀, ∀ f : ↥F₀, f ∈ V₁ ↔ ∃ b c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), c ∉ 𝔭 ∧ f * (c : ↥F₀) = (b : ↥F₀))

    (U : (AlgebraicCurve.TwoChartIntegralModel A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).Opens)
    (hxU : (AlgebraicCurve.TwoChartIntegralModel.ιInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫max.isPrime⟩ ∈ U)
    (hU : Smooth (U.ι ≫ AlgebraicCurve.TwoChartIntegralModel.toBase A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) :
    (∃ (B : Subalgebra A₀ ↥F₀) (𝔪 : Ideal ↥B) (_ : 𝔪.IsMaximal),

      B.FG ∧
      (∀ x : ↥F₀, _root_.IsIntegral ↥B x → x ∈ B) ∧
      (∀ x : ↥F₀, ∃ b c : ↥F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b) ∧
      (∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime → Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬ 𝔮.IsMaximal →
        𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes) ∧
      (∀ 𝔭 : Ideal ↥B, 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔭) →
        ∃ V₁ : ValuationSubring ↥F₀, ∀ f : ↥F₀, f ∈ V₁ ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : ↥F₀) = (b : ↥F₀)) ∧

      (∀ ℓ' : CuspidalType.ProjLine q, (∀ b : ↥B, ((b : ↥F₀) : ↥(fieldBar q M')) ∈ OIg ℓ') → ℓ' = lineInfty q) ∧
      (∀ s : ↥W, ¬ ∀ b : ↥B, ((b : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s) ∧
      (∃ 𝔮 : Ideal ↥B, 𝔮.IsPrime ∧ ∀ x : ↥F₀, (x : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ↔
        ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧
      (∀ 𝔮 : Ideal ↥B, 𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes →
        ∀ x : ↥F₀, (x : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧

      (∀ b : ↥B, (b : ↥F₀) ∈ V) ∧ (∀ b : ↥B, b ∈ 𝔪 ↔ (b : ↥F₀) ∈ V.nonunits) ∧

      ((⟨_, hjF₀⟩ : ↥F₀) ∈ B ∨ (⟨_, hjF₀⟩ : ↥F₀)⁻¹ ∈ B) ∧

      (algebraMap A₀ (Localization.AtPrime 𝔪)).FormallySmooth) := by sorry
