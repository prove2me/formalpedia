-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_igusaNodes_discFamily_of_igusaGaussRing_allInertia_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.exists_igusaNodes_discFamily_of_igusaGaussRing_allInertia_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/168a4a7b-deb3-5ad4-b1e2-e438820953aa
-- title:
--   Igusa nodes and residue discs for q=2
-- statement:
--   Throughout, $q$ is a prime subject to the hypothesis $hq2 : q = 2$, $M'$ is a nonzero natural number with $q \nmid M'$, and $\ell$ is a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$ (a rigidifying auxiliary level prime). Further, $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $q$ in the sense of `LiesOverPrime`, i.e. $q$ is a non-unit of $A$; write $\kappa =$ `ResidueField A` and $\mathrm{res}_A : A \to \kappa$ for the residue map. Two function fields occur: $F_0 =$ `modularFunctionFieldBar M'`, the intermediate field of `LaurentSeries (AlgebraicClosure ℚ)` generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of `modularFunctionFieldFull M'`, and $F =$ `fieldBar q M'` $=$ `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')`, generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of the $q$-expansion function field of level $\Gamma_H(q^2M')$ with $H =$ `levelH q M'` the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, i.e. the units congruent to $1$ modulo $q$. The hypothesis `hle` asserts $F_0 \le F$, and `IntermediateField.inclusion hle` is the resulting embedding. On the residue side the corresponding fields are $\bar F_0 =$ `modularFunctionFieldC κ M'`, generated over $\kappa$ by the reduced $q$-expansions `jqModC κ` and `jqNModC κ M'`, and $\bar F =$ `xHFunctionFieldC κ (q ^ 2 * M') (levelH q M')`.
--
--   The finset $W$ of places of $\bar F_0$ over $\kappa$ is required by `hW` to be exactly `ssPlaces q M' κ`, the set of supersingular places: those places $w$ that are rational (the structure map $\kappa \to$ `w.ResidueField` is surjective), satisfy `IsAffineGeomPlace κ M' w`, and whose $j$-value `w.evalAt (jGeomGen κ M')` lies in `ssJSet q κ`.
--
--   Reduction data. $R_0$ is a `ConstantReduction` of $F_0$ along $A$ with values in $\bar F_0$: a valuation subring `R₀.integers` of $F_0$ together with a surjective ring homomorphism `R₀.residue` onto $\bar F_0$ whose kernel is the maximal ideal, compatible with $A$ and with $\mathrm{res}_A$, admitting scalings of nonzero elements into the integers with nonzero residue, and equipped with a degree-preserving map on places compatible with divisors. The hypothesis `hR₀` says that this reduction is coefficientwise: for every Laurent series $y$ over $A$ whose image in `LaurentSeries (AlgebraicClosure ℚ)` lies in $F_0$, that image lies in `R₀.integers` and its residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$. Further, $R$ is a `RegularProlongation` of $A$ to $F$ with values in $\bar F$ (the same data without the place-theoretic clauses), and `hR` identifies `R.integers` with the Gauss ring $O^{\mathrm{Ig}}_\infty =$ `OIg (lineInfty q)`; `hR₀O` says that an element of $F_0$ lies in `R₀.integers` precisely when its image in $F$ lies in $O^{\mathrm{Ig}}_\infty$. Finally $\pi \in \overline{\mathbb{Q}}$ satisfies $\pi^{q^2-1} = q$ and $\pi \in A$.
--
--   The Igusa rings. A fixed $\zeta \in$ `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$) indexes the level automorphisms `levelAutBar q M' ζ' γ` of $F$ over $\overline{\mathbb{Q}}$. A family $O^{\mathrm{Ig}} : \mathbb{P}^1(\mathbb{Z}/q) \to$ valuation subrings of $F$ is given, subject to four clauses: `hIg_inf` characterises $O^{\mathrm{Ig}}_\infty$ at `lineInfty q` $= [1:0]$ as the Gauss ring, namely $f \in O^{\mathrm{Ig}}_\infty$ if and only if there are Laurent series $x, y$ over $A$ with the coefficientwise reduction of $y$ nonzero and $f \cdot y = x$ in `LaurentSeries (AlgebraicClosure ℚ)`; `hIg` asserts that each point of $\mathbb{P}^1(\mathbb{Z}/q)$ (the bound variable there shadows the prime $\ell$) is of the form `redQ q γ • lineInfty q` for some $\gamma \in \Gamma_0(M')$ with $O^{\mathrm{Ig}}$ at that point equal to the pull-back of $O^{\mathrm{Ig}}_\infty$ along `levelAutBar q M' ζ γ`; `hIg_inj` asserts injectivity of $O^{\mathrm{Ig}}$; and `hIg_perm` asserts that for every $\zeta'$ and every $\gamma \in \Gamma_0(M')$ the pull-backs along `levelAutBar q M' ζ' γ` permute the family, i.e. equal $O^{\mathrm{Ig}}_{\sigma(\cdot)}$ for some permutation $\sigma$ of $\mathbb{P}^1(\mathbb{Z}/q)$.
--
--   The supersingular rings. A family $O^{\mathrm{ss}} : W \to$ valuation subrings of $F$ is given, subject to four clauses. `hSS_A` : for $s \in W$ and $x \in \overline{\mathbb{Q}}$, the image of $x$ lies in $O^{\mathrm{ss}}_s$ if and only if $x \in A$. `hSS_over` : for $s \in W$ and $f \in$ `R₀.integers` such that $f$ is non-negative at every place of $F_0$ over $\overline{\mathbb{Q}}$ at which the $q$-expansion of $j$ (the element of $F_0$ given by `coeffEmb (AlgebraicClosure ℚ) jq`) is non-negative, and such that `R₀.residue f` lies in the valuation subring of $s$, the image of $f$ in $F$ lies in $O^{\mathrm{ss}}_s$, and for every $a \in A$ with $\mathrm{res}_A(a) =$ `s.evalAt (R₀.residue f)` the difference of that image and $a$ lies in $O^{\mathrm{ss}}_s$ and in its maximal ideal. `hSS_fix` : every $O^{\mathrm{ss}}_s$ is invariant under pull-back along every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$. `hSS_tr` : each $O^{\mathrm{ss}}_s$ contains an element $t$ such that $t - a$ is a unit of $O^{\mathrm{ss}}_s$ for every $a \in A$.
--
--   Conclusion. There exist a finset $N^{\mathrm{Ig}}$ of places of $\bar F$ over $\kappa$, a map $\mathrm{disc}$ sending each such place to a set of places of $F$ over $\overline{\mathbb{Q}}$, a map $\mathrm{coord}$ sending each such place to an element of $F$, a map $S$ sending each such place $Q$ to a subring $S(Q)$ of $F$, and for each $Q$ a ring homomorphism $\chi_0(Q) : S(Q) \to \kappa$, such that the following hold.
--
--   (1) $|N^{\mathrm{Ig}}| = |W|$.
--
--   (2) `R.DiscFamily NIg disc coord` : for every $Q \notin N^{\mathrm{Ig}}$ the set $\mathrm{disc}(Q)$ is a residue disc for $R$ above $Q$ with coordinate $\mathrm{coord}(Q)$, in the sense of `IsResidueDisc`, namely the conjunction of `IsDiscCoord`, `PointwiseOn` and `DegreeOn`; and the discs separate points: if $Q, Q' \notin N^{\mathrm{Ig}}$ and some place $P$ lies in both $\mathrm{disc}(Q)$ and $\mathrm{disc}(Q')$, then $Q = Q'$.
--
--   (3) For every $Q \notin N^{\mathrm{Ig}}$: every element of $S(Q)$ lies in `R.integers`; and a place $P$ of $F$ over $\overline{\mathbb{Q}}$ lies in $\mathrm{disc}(Q)$ if and only if $P$ is rational, every $f \in S(Q)$ lies in the valuation subring of $P$ with $P.\mathrm{evalAt}(f) \in A$, and for every $f \in S(Q)$ the valuation of $P.\mathrm{evalAt}(f)$ in $A$ is $< 1$ exactly when $\chi_0(Q)(f) = 0$.
--
--   (4) For every $\tau$ in `A.inertiaSubgroupIn ℚ` (the inertia subgroup of $A$ inside $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$, transported along the decomposition subgroup) and every $Q \notin N^{\mathrm{Ig}}$: the subring $S(Q)$ is stable under the semilinear coefficientwise action [`ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ`](def/ModularCurve_ArithmeticGalois.html#L54) in the strong sense that $f \in S(Q)$ if and only if $\tau \cdot f \in S(Q)$; and $\chi_0(Q)$ is invariant, i.e. $\chi_0(Q)(\tau \cdot f) = \chi_0(Q)(f)$ whenever $f$ and $\tau \cdot f$ lie in $S(Q)$.
--
--   (5) There is a ring homomorphism $j : \bar F_0 \to \bar F$ such that for every $f \in$ `R₀.integers` the image of $f$ in $F$ lies in `R.integers` with `R.residue` of it equal to $j(\mathrm{R₀.residue}(f))$, and such that $Q \in N^{\mathrm{Ig}}$ if and only if there is $s \in W$ with: for all $g \in \bar F_0$, $g$ lies in the valuation subring of $s$ exactly when $j(g)$ lies in the valuation subring of $Q$. Thus the nodes $N^{\mathrm{Ig}}$ are precisely the places of $\bar F$ lying over the supersingular places $W$ through $j$.
--
--   (6) Let $G$ be the subgroup of $\overline{\mathbb{Q}}$-automorphisms of $F$ generated by the level automorphisms `levelAutBar q M' ζ' γ` with $\zeta' \in$ `Idx q` and $\gamma \in \Gamma_0(M')$. For every $\tau \in G$ preserving `R.integers` (hypothesis $h\tau$: $\tau f \in$ `R.integers` iff $f \in$ `R.integers`) and every place $Q$ of $\bar F$: `R.resAut τ hτ • Q` lies in $N^{\mathrm{Ig}}$ if and only if $Q$ does.
--
--   (7) For every such $\tau \in G$ with $h\tau$ and every $Q \notin N^{\mathrm{Ig}}$: `RegularProlongation.smulDisc τ (disc Q)` $= \mathrm{disc}(\mathrm{R.resAut}\,\tau\,h\tau \cdot Q)$, where the left-hand side is $\{P \mid \tau^{-1} \cdot P \in \mathrm{disc}(Q)\}$.
--
--   (8) For every $g \in G$ whose pull-back moves the Gauss ring, i.e. with the pull-back of $O^{\mathrm{Ig}}_\infty$ along $g$ different from $O^{\mathrm{Ig}}_\infty$: for all $Q, Q' \notin N^{\mathrm{Ig}}$ and every $P \in \mathrm{disc}(Q)$, the place $g \cdot P$ does not lie in $\mathrm{disc}(Q')$.
--
--   (9) The discs avoid the supersingular specialisations: for $Q \notin N^{\mathrm{Ig}}$, $P \in \mathrm{disc}(Q)$ and $s \in W$, it is not the case that both of the following hold. First, the image in $F$ of the element `coeffEmb (AlgebraicClosure ℚ) jq` of $F_0$ lies in the valuation subring of $P$ and, for every $a \in A$ with $\mathrm{res}_A(a) =$ `s.evalAt (jGeomGen κ M')`, the difference $P.\mathrm{evalAt}$ of that element minus $a$ lies in $A$ and in the maximal ideal of $A$. Second, the same two conditions with `coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq)` in place of the first element and `jNGeomGen κ M'` in place of `jGeomGen κ M'`.
--
--   (10) Conversely, every place not specialising to a supersingular point is carried into a disc: for every place $P$ of $F$ over $\overline{\mathbb{Q}}$, if for no $s \in W$ it holds that — for every $f \in$ `R₀.integers` which is non-negative at every place of $F_0$ where the $q$-expansion of $j$ is non-negative and whose residue `R₀.residue f` lies in the valuation subring of $s$, and for every $a \in A$ with $\mathrm{res}_A(a) =$ `s.evalAt (R₀.residue f)`, the element $P.\mathrm{evalAt}$ of the image of $f$ in $F$ minus $a$ lies in $A$ and in its maximal ideal — then there are $\gamma \in \Gamma_0(M')$ and $Q \notin N^{\mathrm{Ig}}$ with `levelAutBar q M' ζ γ • P` $\in \mathrm{disc}(Q)$.
--
--   (11) There is a place $P$ of $F$ over $\overline{\mathbb{Q}}$ whose valuation subring is `qIntegersBar (AlgebraicClosure ℚ) (fieldBar q M')`, the subring of elements of non-negative $q$-expansion order, and a $Q \notin N^{\mathrm{Ig}}$ with $P \in \mathrm{disc}(Q)$.
--
--   This is the Igusa-component node law for the semistable covering of the modular curve of level $\Gamma_H(q^2M')$ at a place above $q$ in the case $q = 2$, in the Deligne–Rapoport/Katz–Mazur picture: the nodes on the Igusa component are exactly the places lying over the supersingular places of level $M'$, their number is $|W|$, and away from them the component is covered by a Galois-equivariant family of residue discs with explicit coordinate rings $S(Q)$ and reduction characters $\chi_0(Q)$. It is the input used by [`ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.exists_semistableCovering_equivClauses_of_valuationSubrings_semistableModel_inertiaInfty_charted_of_eq_two_of_dvd) in assembling the semistable covering, and it rests on the étale-chart criterion [`AlgebraicCurve.RegularProlongation.isResidueDisc_of_etaleChart_of_sections`](thm.html#AlgebraicCurve.RegularProlongation.isResidueDisc_of_etaleChart_of_sections) together with the smooth-point charts of [`ModularCurve.FullLevel.exists_igusaSmoothPointCharts_of_igusaGaussRing_allInertia_of_eq_two`](thm.html#ModularCurve.FullLevel.exists_igusaSmoothPointCharts_of_igusaGaussRing_allInertia_of_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_igusaNodes_discFamily_of_igusaGaussRing_allInertia_of_eq_two_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.exists_igusaNodes_discFamily_of_igusaGaussRing_allInertia_of_eq_two_of_dvd
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
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))

    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A) :
    ∃ (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))))
      (disc : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Set (Place (AlgebraicClosure ℚ) (fieldBar q M')))
      (coord : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → (fieldBar q M'))
      (S : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Subring (fieldBar q M'))
      (χ₀ : ∀ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), ↥(S Q) →+* ResidueField A),
      NIg.card = W.card ∧ R.DiscFamily NIg disc coord ∧

      (∀ Q, Q ∉ NIg → (∀ f : ↥(S Q), (f : fieldBar q M') ∈ R.integers) ∧
        ∀ P, P ∈ disc Q ↔ P.IsRational ∧
          (∀ f : ↥(S Q), (f : fieldBar q M') ∈ P.toValuationSubring ∧ P.evalAt (f : fieldBar q M') ∈ A) ∧
          (∀ f : ↥(S Q), A.valuation (P.evalAt (f : fieldBar q M')) < 1 ↔ χ₀ Q f = 0)) ∧

      (∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ Q, Q ∉ NIg →
        (∀ f : fieldBar q M', f ∈ S Q ↔
          ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • f ∈ S Q) ∧
        (∀ (f : ↥(S Q)) (hf : ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : fieldBar q M') ∈ S Q),
          χ₀ Q ⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : fieldBar q M'), hf⟩ = χ₀ Q f)) ∧

      (∃ j : modularFunctionFieldC (ResidueField A) M' →+* xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'),
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers, R.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
        ∀ Q, Q ∈ NIg ↔ ∃ s : ↥W, ∀ g : modularFunctionFieldC (ResidueField A) M',
          g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
            j g ∈ Q.toValuationSubring) ∧
      (∀ τ ∈ (Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}), ∀ (hτ : ∀ f : (fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))),
        R.resAut τ hτ • Q ∈ NIg ↔ Q ∈ NIg) ∧
      (∀ τ ∈ (Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}), ∀ (hτ : ∀ f : (fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))),
        Q ∉ NIg → RegularProlongation.smulDisc τ (disc Q) = disc (R.resAut τ hτ • Q)) ∧

      (∀ g ∈ (Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}), (OIg (lineInfty q)).comap g.toAlgHom.toRingHom ≠ OIg (lineInfty q) →
        ∀ Q Q', Q ∉ NIg → Q' ∉ NIg → ∀ P, P ∈ disc Q → g • P ∉ disc Q') ∧

      (∀ Q, Q ∉ NIg → ∀ P ∈ disc Q, ∀ s : ↥W, ¬ (((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ P.toValuationSubring ∧
          (∀ a : A, residue A a = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jGeomGen (ResidueField A) M') →
            ∃ h : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
              (⟨_, h⟩ : A) ∈ maximalIdeal A)) ∧
        ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ P.toValuationSubring ∧
          (∀ a : A, residue A a = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jNGeomGen (ResidueField A) M') →
            ∃ h : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
              (⟨_, h⟩ : A) ∈ maximalIdeal A)))) ∧

      (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'),
        (∀ s : ↥W, ¬ (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
            (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
            (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
              ∀ a : A, residue A a =
                  (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                  (⟨_, h⟩ : A) ∈ maximalIdeal A)) →
        ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ ∃ Q, Q ∉ NIg ∧ levelAutBar q M' ζ γ • P ∈ disc Q) ∧
      ∃ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P.toValuationSubring = qIntegersBar (AlgebraicClosure ℚ) (fieldBar q M') ∧
        ∃ Q, Q ∉ NIg ∧ P ∈ disc Q := by sorry
