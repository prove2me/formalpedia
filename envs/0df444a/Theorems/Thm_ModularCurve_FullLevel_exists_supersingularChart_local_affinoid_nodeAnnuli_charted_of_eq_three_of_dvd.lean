-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_supersingularChart_local_affinoid_nodeAnnuli_charted_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.exists_supersingularChart_local_affinoid_nodeAnnuli_charted_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/317ea0ab-6421-5472-9058-82465d3faaa6
-- title:
--   Supersingular chart with node annuli at q=3, charted
-- statement:
--   Throughout, a place of $F$ over $K$ (for a field extension $K\subseteq F$) is, in the sense used here, a valuation subring $P\subseteq F$ containing the image of $K$, different from $F$, whose underlying ring is a principal ideal ring; $P.\mathrm{ord}$ is the associated normalised $\mathbb Z$-valued valuation, $P$ is *rational* when $K$ surjects onto the residue field of $P$, and $P.\mathrm{evalAt}\,f\in K$ is then the element representing the residue of $f$ if $f\in P$ (and $0$ otherwise). For a set $D$ of places of `fieldBar q M'` over $\overline{\mathbb Q}$, say that $f$ is *$A$-bounded on $D$* when $f\in P$ and $P.\mathrm{evalAt}\,f\in A$ for every $P\in D$; this is the condition written out literally in the statement.
--
--   **Data and hypotheses.** Let $q$ be a prime with $q=3$, let $M'$ be a nonzero natural number with $q\nmid M'$, and let $\ell$ be a prime with $\ell\equiv 11\pmod{12}$ and $\ell\mid M'$ (the rigid auxiliary level). Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with `A.LiesOverPrime q`, i.e. $q$ is a non-unit of $A$; write $\kappa$ for the residue field of $A$. Here `modularFunctionFieldC` $\kappa\,M'$ is the subfield of $\kappa((t))$ generated over $\kappa$ by the two series `jqModC` $\kappa$ and `jqNModC` $\kappa\,M'$; `modularFunctionFieldBar M'` is the subfield of $\overline{\mathbb Q}((t))$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of `modularFunctionFieldFull M'`; and `fieldBar q M'` is the corresponding base change to $\overline{\mathbb Q}$ of `xHFunctionField` $(q^2M')$ `(levelH q M')`, where `levelH q M'` is the kernel of the reduction $(\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times$, that is, the group of units congruent to $1$ modulo $q$.
--
--   The further hypotheses are: a finset $W$ of places of `modularFunctionFieldC` $\kappa\,M'$ over $\kappa$ together with `hW`, which says that $W$ is exactly the set `ssPlaces q M'` $\kappa$ of supersingular places, i.e. of those places $w$ that are rational, satisfy the predicate `IsAffineGeomPlace`, and have $w.\mathrm{evalAt}(\mathtt{jGeomGen}\ \kappa\ M')$ in `ssJSet q` $\kappa$; an inclusion `hle` of `modularFunctionFieldBar M'` in `fieldBar q M'`; a constant reduction $R_0$ of `modularFunctionFieldBar M'` along $A$ with reduced field `modularFunctionFieldC` $\kappa\,M'$, that is, a valuation subring $R_0.\mathrm{integers}$ of `modularFunctionFieldBar M'`, a surjective ring homomorphism $R_0.\mathrm{residue}$ from it onto `modularFunctionFieldC` $\kappa\,M'$ whose kernel is the maximal ideal, a map on places preserving degrees, the requirement that a constant $x\in\overline{\mathbb Q}$ lies in $R_0.\mathrm{integers}$ exactly when $x\in A$ and that constants reduce through $\kappa$, the scaling clause that every nonzero $f$ has a constant multiple in $R_0.\mathrm{integers}$ with nonzero residue, and compatibility of divisors with the map on places; the hypothesis `hR₀`, which says that for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb Q}((t))$ lies in `modularFunctionFieldBar M'`, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$; and finally an element $s$ of $W$, i.e. a supersingular place.
--
--   **Conclusion.** There exist a field $FSS$ which is a $\kappa$-algebra, a component chart $C$ of `fieldBar q M'` along $A$ with reduced field $FSS$ — so a valuation subring $C.\mathrm{integers}$, a surjective residue homomorphism onto $FSS$ with kernel the maximal ideal, a set $C.\mathrm{dom}$ of places of `fieldBar q M'` over $\overline{\mathbb Q}$, a finset $C.\mathrm{nodes}$ of places of $FSS$ over $\kappa$, a map $C.\mathrm{placeMap}$ on places avoiding the nodes on $C.\mathrm{dom}$, the $A$-compatibility of constants, the scaling clause, the pointwise compatibility of $P.\mathrm{evalAt}$ with the residue at $C.\mathrm{placeMap}\,P$, and the divisor push-forward away from the nodes — and a finset $N$ of places of $FSS$ over $\kappa$, such that all of the following hold.
--
--   (1) Some $t\in FSS$ is transcendental over $\kappa$.
--
--   (2) ($C$ prolongs $R_0$ at $s$.) For every $f\in R_0.\mathrm{integers}$ such that $0\le P.\mathrm{ord}\,f$ at every place $P$ of `modularFunctionFieldBar M'` over $\overline{\mathbb Q}$ at which the coefficientwise image of the $q$-expansion `jq` of the modular invariant $j$ has non-negative order, and such that $R_0.\mathrm{residue}\,f$ lies in the valuation subring of $s$: the image of $f$ in `fieldBar q M'` lies in $C.\mathrm{integers}$, and its $C$-residue is the image under $\kappa\to FSS$ of $s.\mathrm{evalAt}(R_0.\mathrm{residue}\,f)$.
--
--   (3) (Invariance of the chart ring.) For every $\zeta$ in `Idx q`, the set of primitive $q$-th roots of unity in $\overline{\mathbb Q}$, and every $\gamma\in SL_2(\mathbb Z)$ with $\gamma\in\Gamma_0(M')$, the pullback of $C$ along the automorphism `levelAutBar q M' ζ γ` of `fieldBar q M'` over $\overline{\mathbb Q}$ has the same ring of integers as $C$.
--
--   (4) $N$ has exactly $q+1$ elements.
--
--   (5) (Residue discs and cusp-freeness.) For every place $Q$ of $FSS$ over $\kappa$ with $Q\notin N$: there is $T\in C.\mathrm{integers}$ with $C.\mathrm{residue}\,T\ne 0$ and $Q.\mathrm{ord}(C.\mathrm{residue}\,T)=1$ such that, for every $P\in C.\mathrm{dom}$ with $C.\mathrm{placeMap}\,P=Q$, one has $T\in P$ and $P.\mathrm{evalAt}\,T\in A$ lying in the maximal ideal of $A$, and such that for every $c$ in the maximal ideal of $A$ there is exactly one place $P$ of `fieldBar q M'` over $\overline{\mathbb Q}$ with $P\in C.\mathrm{dom}$, $C.\mathrm{placeMap}\,P=Q$ and $P.\mathrm{evalAt}\,T=c$; moreover every $P\in C.\mathrm{dom}$ with $C.\mathrm{placeMap}\,P=Q$ has non-negative order on the image in `fieldBar q M'` of the coefficientwise image of `jq`.
--
--   (6) (Invariance of the domain.) For every $\zeta$ and every $\gamma\in\Gamma_0(M')$, the pullback of $C$ along `levelAutBar q M' ζ γ` has the same domain as $C$.
--
--   (7) (Affinoid description.) Every $f\in$ `fieldBar q M'` that is $A$-bounded on $C.\mathrm{dom}$ lies in $C.\mathrm{integers}$; and every $g\in FSS$ lying in the valuation subring of every $Q\notin N$ is the $C$-residue of some $f\in C.\mathrm{integers}$ which is $A$-bounded on $C.\mathrm{dom}$.
--
--   (8) (Localisation.) Every $h\in C.\mathrm{integers}$ can be written as $h\cdot s'=r$ with $r$ and $s'$ both $A$-bounded on $C.\mathrm{dom}$, $s'\in C.\mathrm{integers}$ and $C.\mathrm{residue}\,s'\ne 0$.
--
--   (9) Every place in $C.\mathrm{dom}$ is rational.
--
--   (10) (Dictionary of places.) Writing $\mathcal O$ for the intersection, inside $FSS$, of the valuation subrings of all places $Q\notin N$: every maximal ideal $\mathfrak m$ of $\mathcal O$ determines a unique $Q\notin N$ with $\mathfrak m=\{g: g=0\text{ or } 0<Q.\mathrm{ord}\,g\}$, and conversely every $Q\notin N$ arises from such a maximal ideal.
--
--   (11) For every $f\in C.\mathrm{integers}$ that is $A$-bounded on $C.\mathrm{dom}$ and every $Q\notin N$, the residue $C.\mathrm{residue}\,f$ lies in the valuation subring of $Q$.
--
--   (12) (Dimension one.) Every nonzero prime ideal of $\mathcal O$ is maximal.
--
--   (13) (Level translates separate the points off $N$.) For every $Q\notin N$ there are $\zeta$ and $\gamma\in\Gamma_0(M')$ and an $f\in C.\mathrm{integers}$, $A$-bounded on $C.\mathrm{dom}$, whose image under `levelAutBar q M' ζ γ` also lies in $C.\mathrm{integers}$, with $0<Q.\mathrm{ord}(C.\mathrm{residue}\,f)$ and $0<Q.\mathrm{ord}$ of the residue of the translate failing.
--
--   (14) (Node annuli.) There is a family $An$ assigning to each $x\in N$ an annulus $An(x)$ of `fieldBar q M'` over $A$ — that is, a set $An(x).\mathrm{dom}$ of places, a parameter, and a modulus in the maximal ideal of $A$, subject to the annulus axioms: each place of the domain is rational, holds the parameter with value in the maximal ideal of $A$, nonzero, and dividing the modulus within the maximal ideal; each admissible value in the maximal ideal is attained by exactly one place of the domain; the parameter minus its value has order $1$ at each place of the domain; and the unit principle for functions of order $0$ throughout the domain — such that:
--
--   (ATT) each $An(x)$ is attached to $C$ at $x$: $x\in C.\mathrm{nodes}$, the parameter lies in $C.\mathrm{integers}$ with $x.\mathrm{ord}$ of its residue equal to $1$, and for every $f\in C.\mathrm{integers}$ with nonzero residue and order $0$ at all places of $An(x).\mathrm{dom}$, at each such place $P$ the element $P.\mathrm{evalAt}\,f\cdot (P.\mathrm{evalAt}\,\mathrm{param})^{-x.\mathrm{ord}(C.\mathrm{residue}\,f)}$ lies in $A$ and is a unit there;
--
--   (MOVE) for each $x\in N$ there are $\zeta$ and $\gamma\in\Gamma_0(M')$ and some $x'\in N$ with $x'\ne x$ such that the pullback of $An(x)$ along `levelAutBar q M' ζ γ` has domain equal to $An(x').\mathrm{dom}$;
--
--   (SEP) for every valuation subring $O$ of `fieldBar q M'` and all $x,x'\in N$: if a constant of $\overline{\mathbb Q}$ lies in $O$ exactly when it lies in $A$, if some $t\in O$ has $t-a$ a unit of $O$ for every $a\in A$, if not every $f$ that is $A$-bounded on $C.\mathrm{dom}$ lies in $O$, while every $f$ that is $A$-bounded on $An(x).\mathrm{dom}$ and every $f$ that is $A$-bounded on $An(x').\mathrm{dom}$ does lie in $O$, then $x=x'$;
--
--   (charted type-II exhaustion) for every field $F_o$ that is a $\kappa$-algebra with `IsCurveOver` $\kappa\,F_o$ — so principal divisors of degree zero exist, all residue fields of places are finite over $\kappa$, and $\Omega_{F_o/\kappa}$ is free of rank $1$ — and essentially of finite type over $\kappa$, and for every component chart $C_o$ of `fieldBar q M'` along $A$ with reduced field $F_o$: if $C_o$ is centred over $s$, in the sense that for every $f\in R_0.\mathrm{integers}$ satisfying the two conditions of (2) the image of $f$ lies in $C_o.\mathrm{integers}$ and, for every $a\in A$ whose residue equals $s.\mathrm{evalAt}(R_0.\mathrm{residue}\,f)$, the difference of that image and $a$ lies in $C_o.\mathrm{integers}$ and in the maximal ideal of $C_o.\mathrm{integers}$ — then either every $f$ that is $A$-bounded on $C.\mathrm{dom}$ lies in $C_o.\mathrm{integers}$, or there is $x\in N$ such that every $f$ that is $A$-bounded on $An(x).\mathrm{dom}$ lies in $C_o.\mathrm{integers}$.
--
--   This is the supersingular-chart input to the semistable reduction analysis of the full-level modular curve for $\Gamma(q)\cap\Gamma_0(M')$ at $q=3$: over a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $3$ and a supersingular place $s$ of the modular function field in characteristic $3$, it produces the component of the reduction, its $q+1$ exceptional points, the residue discs and the annuli joining it to its level translates. It differs from the unrestricted form of the statement in that the final exhaustion clause quantifies only over the Gauss rings of component charts whose reduced field is a curve over the residue field of $A$, which is the form used by [`ModularCurve.FullLevel.componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq_of_eq_three_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_supersingularChart_local_affinoid_nodeAnnuli_charted_of_eq_three_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_supersingularChart_local_affinoid_nodeAnnuli_charted_of_eq_three_of_dvd
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
    (s : ↥W) :
    ∃ (FSS : Type) (_ : Field FSS) (_ : Algebra (ResidueField A) FSS)
      (C : ComponentChart A (fieldBar q M') FSS) (N : Finset (Place (ResidueField A) FSS)),
      (∃ t : FSS, Transcendental (ResidueField A) t) ∧
      (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ C.integers,
            C.residue ⟨_, hC⟩ = algebraMap (ResidueField A) FSS
              ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
                (R₀.residue ⟨f, hf⟩))) ∧
      (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → (C.comap (levelAutBar q M' ζ γ)).integers = C.integers) ∧

      N.card = q + 1 ∧
      (∀ Q : Place (ResidueField A) FSS, Q ∉ N →
        (∃ (T : ↥(fieldBar q M')) (hT : T ∈ C.integers), C.residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord (C.residue ⟨T, hT⟩) = 1 ∧
          (∀ P ∈ C.dom, C.placeMap P = Q → T ∈ P.toValuationSubring ∧
            ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
          ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
            ∃! P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ C.dom ∧ C.placeMap P = Q ∧ P.evalAt T = c) ∧
        ∀ P ∈ C.dom, C.placeMap P = Q →
          0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : fieldBar q M')) ∧

      (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → (C.comap (levelAutBar q M' ζ γ)).dom = C.dom) ∧

      ((∀ f : ↥(fieldBar q M'), (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ C.integers) ∧
        ∀ g : FSS, (∀ Q : Place (ResidueField A) FSS, Q ∉ N → g ∈ Q.toValuationSubring) →
          ∃ (f : ↥(fieldBar q M')) (hf : f ∈ C.integers),
            (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) ∧ C.residue ⟨f, hf⟩ = g) ∧

      (∀ h : ↥(fieldBar q M'), h ∈ C.integers → ∃ (r s' : ↥(fieldBar q M')) (hs' : s' ∈ C.integers),
        (∀ P ∈ C.dom, r ∈ P.toValuationSubring ∧ P.evalAt r ∈ A) ∧ (∀ P ∈ C.dom, s' ∈ P.toValuationSubring ∧ P.evalAt s' ∈ A) ∧
          C.residue ⟨s', hs'⟩ ≠ 0 ∧ h * s' = r) ∧

      (∀ P ∈ C.dom, P.IsRational) ∧

      ((∀ 𝔪 : Ideal ↥(⨅ (Q : Place (ResidueField A) FSS) (_ : Q ∉ N), Q.toValuationSubring.toSubring), 𝔪.IsMaximal →
          ∃! Q : Place (ResidueField A) FSS, Q ∉ N ∧
            ∀ g : ↥(⨅ (Q : Place (ResidueField A) FSS) (_ : Q ∉ N), Q.toValuationSubring.toSubring), g ∈ 𝔪 ↔ (g : FSS) = 0 ∨ 0 < Q.ord (g : FSS)) ∧
        ∀ Q : Place (ResidueField A) FSS, Q ∉ N →
          ∃ 𝔪 : Ideal ↥(⨅ (Q : Place (ResidueField A) FSS) (_ : Q ∉ N), Q.toValuationSubring.toSubring), 𝔪.IsMaximal ∧
            ∀ g : ↥(⨅ (Q : Place (ResidueField A) FSS) (_ : Q ∉ N), Q.toValuationSubring.toSubring), g ∈ 𝔪 ↔ (g : FSS) = 0 ∨ 0 < Q.ord (g : FSS)) ∧

      (∀ (f : ↥(fieldBar q M')) (hf : f ∈ C.integers), (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) →
        ∀ Q : Place (ResidueField A) FSS, Q ∉ N → C.residue ⟨f, hf⟩ ∈ Q.toValuationSubring) ∧

      (∀ 𝔭 : Ideal ↥(⨅ (Q : Place (ResidueField A) FSS) (_ : Q ∉ N), Q.toValuationSubring.toSubring),
        𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭.IsMaximal) ∧

      (∀ Q : Place (ResidueField A) FSS, Q ∉ N →
        ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧
          ∃ (f : ↥(fieldBar q M')) (hf : f ∈ C.integers) (hf' : levelAutBar q M' ζ γ f ∈ C.integers),
            (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) ∧
            0 < Q.ord (C.residue ⟨f, hf⟩) ∧ ¬ 0 < Q.ord (C.residue ⟨levelAutBar q M' ζ γ f, hf'⟩)) ∧

      ∃ An : ↥N → Annulus A ↥(fieldBar q M'),

        (∀ x : ↥N, (An x).IsAttached C (x : Place (ResidueField A) FSS)) ∧

        (∀ x : ↥N, ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ ∃ x' : ↥N, x' ≠ x ∧
          ((An x).comap (levelAutBar q M' ζ γ)).dom = (An x').dom) ∧

        (∀ (O : ValuationSubring ↥(fieldBar q M')) (x x' : ↥N),
          (∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ O ↔ x ∈ A) →
          (∃ t : ↥(fieldBar q M'), t ∈ O ∧ ∀ a : A,
          ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ O, IsUnit (⟨_, h⟩ : O)) →
          ¬ (∀ f : ↥(fieldBar q M'), (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ O) →
          (∀ f : ↥(fieldBar q M'), (∀ P ∈ (An x).dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ O) →
          (∀ f : ↥(fieldBar q M'), (∀ P ∈ (An x').dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ O) → x = x') ∧

        (∀ (Fo : Type) (_ : Field Fo) (_ : Algebra (ResidueField A) Fo)
          (_ : IsCurveOver (ResidueField A) Fo) (_ : Algebra.EssFiniteType (ResidueField A) Fo)
          (Co : ComponentChart A (fieldBar q M') Fo),
          (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          (IntermediateField.inclusion hle f : fieldBar q M') ∈ Co.integers ∧
          ∀ a : A, residue A a =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
                - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ Co.integers,
              (⟨_, h⟩ : Co.integers) ∈ maximalIdeal Co.integers) →
          (∀ f : ↥(fieldBar q M'), (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ Co.integers) ∨
          ∃ x : ↥N, (∀ f : ↥(fieldBar q M'), (∀ P ∈ (An x).dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ Co.integers)) := by sorry
