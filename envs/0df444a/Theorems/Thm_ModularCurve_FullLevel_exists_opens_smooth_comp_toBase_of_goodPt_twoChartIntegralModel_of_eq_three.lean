-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_of_eq_three
-- name    : ModularCurve.FullLevel.exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/2eea5059-21ca-525a-bff6-dc8189e2b125
-- title:
--   Good points of the q=3 two-chart integral model are smooth
-- statement:
--   Throughout, $q$ is a prime with $q=3$ and $M'$ a nonzero natural number with $q \nmid M'$, and $A$ is a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` lying over $q$ in the sense of `LiesOverPrime`, i.e. $q$ lies in `A.nonunits`. Two function fields occur: `modularFunctionFieldBar M'`, the intermediate field of $\overline{\mathbb Q}((t))$ obtained by adjoining to $\overline{\mathbb Q}$ the coefficientwise images of the full level-$M'$ modular function field over $\mathbb Q$, and `fieldBar q M'`, the corresponding base change of the function field of $X_H(q^2M')$ with $H =$ `levelH q M'` the kernel of the reduction $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$; `hle` asserts the inclusion `modularFunctionFieldBar M' ≤ fieldBar q M'`. On the residue side, `modularFunctionFieldC (ResidueField A) M'` is the field generated over the residue field of $A$ by the $q$-expansions of $j$ and $j_{M'}$, and `xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')` the analogous level-$H$ field. A finite set $W$ of places (in the sense of the project's `Place` structure: a valuation subring containing the constants, proper, with principal ideals) of `modularFunctionFieldC (ResidueField A) M'` over `ResidueField A` is given, and `hW` says that $W$ consists exactly of the supersingular places `ssPlaces q M' (ResidueField A)`, those rational affine geometric places whose value at the geometric $j$-generator lies in `ssJSet q`, the set of $j$ such that every elliptic curve with that invariant has no nonzero $q$-torsion point.
--
--   Reduction data. $R_0$ is a `ConstantReduction` of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC (ResidueField A) M'`: a valuation subring $R_0.\mathrm{integers}$, a surjective residue homomorphism onto the residue-field function field whose kernel is the maximal ideal, inducing on constants the reduction $A \to$ `ResidueField A`, together with the scaling condition `exists_smul_mem` and a degree-preserving map on places compatible with orders of functions. The hypothesis `hR₀` identifies $R_0$ on integral Laurent series: for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb Q}((t))$ lies in `modularFunctionFieldBar M'`, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over `ResidueField A`, is the coefficientwise reduction of $y$. The hypothesis `hR₀O` says that $f \in R_0.\mathrm{integers}$ if and only if its image in `fieldBar q M'` lies in $\mathcal O_{\mathrm{Ig}} :=$ `OIg (lineInfty q)`.
--
--   Igusa branches. $\zeta$ is an element of `Idx q`, a primitive $q$-th root of unity in $\overline{\mathbb Q}$, and `OIg` assigns a valuation subring of `fieldBar q M'` to each point of the projective line [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21) over $\mathbb Z/q$. Four hypotheses govern it: `hIg_inf` describes the ring at the point `lineInfty q` as a Gauss ring, $f$ belonging to it exactly when there are Laurent series $x,y$ over $A$ with $y$ having nonzero reduction and $f \cdot \bar y = \bar x$ after pushing coefficients into $\overline{\mathbb Q}$; `hIg` says each point $\ell$ is reached from `lineInfty q` by some $\gamma \in \Gamma_0(M')$ under `redQ q`, with `OIg ℓ` the pullback of `OIg (lineInfty q)` along `levelAutBar q M' ζ γ`; `hIg_inj` says `OIg` is injective; `hIg_perm` says that for every $\zeta'$ and every $\gamma \in \Gamma_0(M')$ the pullbacks along `levelAutBar q M' ζ' γ` permute the family `OIg`.
--
--   Supersingular rings. `OSS` assigns a valuation subring of `fieldBar q M'` to each $s \in W$. The hypothesis `hSS_A` says a constant from $\overline{\mathbb Q}$ lies in `OSS s` exactly when it lies in $A$. The hypothesis `hSS_over` says: for $s \in W$ and $f \in R_0.\mathrm{integers}$ which is regular at every place of `modularFunctionFieldBar M'` at which the $q$-expansion $j_q$ is regular, if the $R_0$-residue of $f$ lies in the valuation subring of the place $s$, then the image of $f$ in `fieldBar q M'` lies in `OSS s`, and moreover for every $a \in A$ whose reduction equals the value of $s$ at that residue, the difference of $f$ and $a$ lies in the maximal ideal of `OSS s`. The hypothesis `hSS_fix` says each `OSS s` is invariant under pullback along `levelAutBar q M' ζ' γ` for all $\zeta'$ and $\gamma \in \Gamma_0(M')$, and `hSS_tr` provides for each $s$ an element $t \in$ `OSS s` such that $t - a$ is a unit of `OSS s` for every $a \in A$.
--
--   Further data. $R$ is a `RegularProlongation` of $A$ from `fieldBar q M'` to `xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')` (a valuation subring with a surjective residue map whose kernel is the maximal ideal, compatible with reduction on constants and satisfying `exists_smul_mem`), and `hR` says $R.\mathrm{integers} =$ `OIg (lineInfty q)`. An element $\pi \in A$ with $\pi^{q^2-1} = q$ is given. A base field $k_0 \subseteq \overline{\mathbb Q}$ is given together with $\pi_0 \in k_0 \cap A$ such that the contraction of $A$ to $k_0$ is a discrete valuation ring with maximal ideal generated by $\pi_0$, is henselian, has algebraically closed residue field, and such that (`hκ`) every element of $A$ is congruent modulo the maximal ideal of $A$ to an element of $k_0 \cap A$. An auxiliary prime $\ell \ge 3$ with $\ell \neq q$ and $\ell \nmid M'$ is given, together with $\zeta_0 \in k_0$ a primitive $(q\ell)$-th root of unity and $\varpi_t \in k_0 \cap A$ with $\varpi_t^{q^2-1} = q u$ for some unit $u$ of $A$. Finally $K_1$ is a finite extension of $k_0$ inside $\overline{\mathbb Q}$ and $A_1$ a valuation subring of $K_1$ cut out by $A$ (`hA₁`), assumed to be a henselian discrete valuation ring.
--
--   Conclusion. With $k_0$ acting on `fieldBar q M'` through $\overline{\mathbb Q}$, the assertion is the following. Let $F_0$ be an intermediate field of $k_0 \subseteq$ `fieldBar q M'` such that: the join of $F_0$ with the $k_0$-subfield generated by all constants from $\overline{\mathbb Q}$ is everything; $F_0$ is stable under every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$; for every finite extension $K'$ of $k_0$ in $\overline{\mathbb Q}$, every finite family $c : \mathrm{Fin}\,m \to \overline{\mathbb Q}$ linearly independent over $K'$ and every family $a$ of elements of the join of $F_0$ with the $k_0$-subfield generated by the image of $K'$, the vanishing of $\sum_i c_i a_i$ forces all $a_i = 0$; and every element of `fieldBar q M'` whose Laurent series has rational coefficients (lies in the range of `coeffEmb`) belongs to $F_0$. Write $T_1$ for the join of $F_0$ with the $k_0$-subfield of `fieldBar q M'` generated by the image of $K_1$. Let $T_1$ carry an $A_1$-algebra structure whose structure map agrees, after inclusion into `fieldBar q M'`, with the constant embedding of $\overline{\mathbb Q}$ applied to $A_1 \subseteq K_1$, and let $j_1 \in T_1$ be nonzero with image in `fieldBar q M'` equal to the element $j_q$ of `modularFunctionFieldBar M'` (the Laurent expansion `coeffEmb (AlgebraicClosure ℚ) jq`) under `hle`. Consider the two-chart integral model [`AlgebraicCurve.TwoChartIntegralModel A₁ T₁ j₁`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), the pushout of the two affine charts given by the integral closures `chartAlgFin` of $A_1[j_1]$ and `chartAlgInf` of $A_1[j_1^{-1}]$ in $T_1$, with its structure morphism `toBase` to $\operatorname{Spec} A_1$.
--
--   Call a point $x$ of this model good when the five following conditions hold: (i) `toBase` maps $x$ to the closed point of $\operatorname{Spec} A_1$; (ii) $x$ is a closed point, i.e. any $y$ with $x \rightsquigarrow y$ equals $x$; (iii) for every point $y$ of the chart $\operatorname{Spec}(\mathrm{chartAlgFin})$ mapping to $x$, every element of `chartAlgFin` whose image in `fieldBar q M'` lies in the nonunits of $R.\mathrm{integers}$ lies in the prime $y$; (iv) the same condition for the chart $\operatorname{Spec}(\mathrm{chartAlgInf})$; (v) for every point $y$ of $\operatorname{Spec}(\mathrm{chartAlgFin})$ mapping to $x$, every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from `chartAlgFin` to $\Omega$ with kernel $y$, the value $\varphi(j_1)$ does not lie in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7).
--
--   Then for every good point $x$ there exists an open subscheme $U$ of the two-chart integral model with $x \in U$ such that the open immersion $U.\iota$ followed by `toBase` is a smooth morphism to $\operatorname{Spec} A_1$.
--
--   This is the per-point smoothness criterion for the two-chart integral model of the level-$H$ modular curve in the case $q = 3$: a closed point of the special fibre that lies on the $\infty$-Igusa branch (conditions (iii), (iv)) and above a non-supersingular $j$-invariant (condition (v)) has a neighbourhood smooth over the base discrete valuation ring $A_1$. It is used by the descent form of the same statement and by the construction of étale coordinates at points off the branch locus in the $q = 3$ strand of the semistable-covering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_of_eq_three.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve IsLocalRing CongruenceSubgroup
open ModularCurve.FullLevel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_of_eq_three
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
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))

    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ₀ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [IsDiscreteValuationRing ↥A₁] [HenselianLocalRing ↥A₁] :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →

    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],

    let GoodPt : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base x = closedPoint ↥A₁ ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), x ⤳ y → y = x) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω)

    ∀ (x : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)), GoodPt x →
      ∃ U : (AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).Opens,
        x ∈ U ∧ Smooth (U.ι ≫ AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) := by sorry
