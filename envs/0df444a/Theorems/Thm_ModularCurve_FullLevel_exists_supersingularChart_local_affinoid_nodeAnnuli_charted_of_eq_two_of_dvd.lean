-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_supersingularChart_local_affinoid_nodeAnnuli_charted_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.exists_supersingularChart_local_affinoid_nodeAnnuli_charted_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/2041c1f5-03c6-5812-ba2b-a03ddc60f840
-- title:
--   Supersingular chart and node annuli at q=2, charted
-- statement:
--   Throughout, $q$ is a prime subject to the hypothesis `hq2 : q = 2`, $M'$ a nonzero natural number with $q \nmid M'$ (`hqM'`), and $\ell$ a prime with $\ell \equiv 11 \pmod{12}$ (`hℓ12`) dividing $M'$ (`hℓM'`). Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ satisfying `hA : A.LiesOverPrime q`, which says that $q$ is a non-unit of $A$; write $\kappa$ for the residue field of $A$ and $\mathrm{res}_A$ for the reduction map $A \to \kappa$.
--
--   Three function fields occur. First, $\mathcal{M}_\kappa :=$ `modularFunctionFieldC κ M'`, the intermediate field of the Laurent series field over $\kappa$ generated over $\kappa$ by the formal $j$-series `jqModC κ` and by its $M'$-fold expansion `jqNModC κ M'`. Second, $F_{\mathrm{full}} :=$ `modularFunctionFieldBar M'`, the base change to $\overline{\mathbb{Q}}$ of the full level-$M'$ modular function field, i.e. the subfield of $\overline{\mathbb{Q}}((T))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of `modularFunctionFieldFull M'`. Third, $\bar F :=$ `fieldBar q M'`, the base change to $\overline{\mathbb{Q}}$ of the function field of $X_H$ of level $q^2M'$, where $H =$ `levelH q M'` is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, that is, the units congruent to $1$ modulo $q$. The hypothesis `hle` asserts $F_{\mathrm{full}} \le \bar F$, and `IntermediateField.inclusion hle` is the resulting embedding. Places are always places in the sense of the project's `Place` structure: valuation subrings of the larger field, containing the image of the base field, proper, and with principal ideal ring structure; `P.ord` is the associated normalised order function, `P.evalAt` evaluation in the base field through the residue field of $P$ (defined by a chosen inverse of the structure map, hence meaningful for rational places, where that map is surjective), and `P.IsRational` says that the structure map from the base field to the residue field of $P$ is surjective.
--
--   A finset $W$ of places of $\mathcal{M}_\kappa$ over $\kappa$ is given, and `hW` identifies its members with the supersingular places `ssPlaces q M' κ`: those places $w$ that are rational, satisfy the predicate `IsAffineGeomPlace κ M'`, and have $w.\mathrm{evalAt}$ of the element `jGeomGen κ M'` lying in the set `ssJSet q κ`. An element $s \in W$ is fixed.
--
--   The datum $R_0$ is a `ConstantReduction A F_full 𝓜_κ`: a valuation subring $R_0.\mathrm{integers}$ of $F_{\mathrm{full}}$, a surjective ring homomorphism $R_0.\mathrm{residue}$ from it onto $\mathcal{M}_\kappa$ with kernel the maximal ideal, a map on places, compatibility of membership and of residues with $A \subseteq \overline{\mathbb{Q}}$ and $\mathrm{res}_A$, a scaling property making every nonzero element reducible to something nonzero, preservation of degrees of places, and compatibility of divisors with the map on places. The hypothesis `hR₀` pins $R_0$ down as coefficientwise reduction: for every Laurent series $y$ with coefficients in $A$ whose coefficientwise image in $\overline{\mathbb{Q}}((T))$ lies in $F_{\mathrm{full}}$, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$.
--
--   Write $J \in F_{\mathrm{full}}$ for the image under `coeffEmb (AlgebraicClosure ℚ)` of the $q$-expansion `jq` of the modular invariant, and say that $f \in \bar F$ is *bounded on a set $D$ of places of $\bar F$ over $\overline{\mathbb{Q}}$* if for every $P \in D$ one has $f \in P.\mathrm{toValuationSubring}$ and $P.\mathrm{evalAt}\,f \in A$ (this condition is written out in full at each occurrence in the Lean statement).
--
--   The conclusion asserts the existence of a field $F_{ss}$ with a $\kappa$-algebra structure, a component chart $C :$ `ComponentChart A (fieldBar q M') FSS` (a valuation subring $C.\mathrm{integers}$ of $\bar F$ with surjective residue map onto $F_{ss}$ having the maximal ideal as kernel, a set $C.\mathrm{dom}$ of places of $\bar F$ over $\overline{\mathbb{Q}}$, a finset $C.\mathrm{nodes}$ of places of $F_{ss}$ over $\kappa$, a map $C.\mathrm{placeMap}$ on places avoiding the nodes on $C.\mathrm{dom}$, the compatibilities with $A$ and $\mathrm{res}_A$, a pointwise compatibility of evaluation with reduction, and a divisor-pushforward property off the nodes), together with a finset $N$ of places of $F_{ss}$ over $\kappa$, such that all of the following hold.
--
--   (1) $F_{ss}$ contains an element transcendental over $\kappa$.
--
--   (2) (Centring over $s$.) For every $f \in R_0.\mathrm{integers}$ such that $0 \le P.\mathrm{ord}(f)$ for every place $P$ of $F_{\mathrm{full}}$ over $\overline{\mathbb{Q}}$ with $0 \le P.\mathrm{ord}(J)$, and such that the $R_0$-residue of $f$ lies in the valuation subring of $s$, the image of $f$ in $\bar F$ lies in $C.\mathrm{integers}$ and its $C$-residue is the image under $\kappa \to F_{ss}$ of $s.\mathrm{evalAt}$ applied to the $R_0$-residue of $f$.
--
--   (3) For every $\zeta \in$ `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$) and every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M')$, the integers of the pullback chart $C.\mathrm{comap}$ along the automorphism `levelAutBar q M' ζ γ` coincide with $C.\mathrm{integers}$; by the definition of `comap` this is the statement that $C.\mathrm{integers}$ is stable under that automorphism. Here `levelAutBar q M' ζ γ` is the $\overline{\mathbb{Q}}$-automorphism of $\bar F$ characterised by the predicate `IsLevelAutBar`, which prescribes its effect on $q$-expansions of modular forms of level $H$ twisted by `conjElem q γ` under any embedding sending $\zeta$ to $e^{2\pi i/q}$, and is the identity if no automorphism satisfies that characterisation.
--
--   (4) $\#N = q+1$.
--
--   (5) For every place $Q$ of $F_{ss}$ over $\kappa$ with $Q \notin N$: there is $T \in C.\mathrm{integers}$ with $C$-residue nonzero and $Q.\mathrm{ord}$ of that residue equal to $1$, such that every $P \in C.\mathrm{dom}$ with $C.\mathrm{placeMap}\,P = Q$ has $T$ in its valuation subring and $P.\mathrm{evalAt}\,T \in A$ with value in the maximal ideal of $A$, and such that for every $c$ in the maximal ideal of $A$ there is exactly one place $P$ of $\bar F$ over $\overline{\mathbb{Q}}$ with $P \in C.\mathrm{dom}$, $C.\mathrm{placeMap}\,P = Q$ and $P.\mathrm{evalAt}\,T = c$; moreover every $P \in C.\mathrm{dom}$ with $C.\mathrm{placeMap}\,P = Q$ satisfies $0 \le P.\mathrm{ord}$ of the image of $J$ in $\bar F$.
--
--   (6) For every $\zeta$ and every $\gamma \in \Gamma_0(M')$, the domain of $C.\mathrm{comap}$ along `levelAutBar q M' ζ γ` equals $C.\mathrm{dom}$, i.e. $C.\mathrm{dom}$ is stable under the induced action on places.
--
--   (7) Every $f \in \bar F$ bounded on $C.\mathrm{dom}$ lies in $C.\mathrm{integers}$; and every $g \in F_{ss}$ lying in the valuation subring of every place $Q \notin N$ is the $C$-residue of some $f \in C.\mathrm{integers}$ bounded on $C.\mathrm{dom}$.
--
--   (8) Every $h \in C.\mathrm{integers}$ can be written as a quotient in the following sense: there are $r, s' \in \bar F$ with $s' \in C.\mathrm{integers}$, both bounded on $C.\mathrm{dom}$, with $C$-residue of $s'$ nonzero and $h \cdot s' = r$.
--
--   (9) Every $P \in C.\mathrm{dom}$ is rational.
--
--   (10) For the subring $\bigcap_{Q \notin N} Q.\mathrm{toValuationSubring}$ of $F_{ss}$: every maximal ideal $\mathfrak{m}$ of it is of the form associated with exactly one place $Q \notin N$, the association being that $g \in \mathfrak{m}$ if and only if $g = 0$ or $0 < Q.\mathrm{ord}(g)$; and conversely every $Q \notin N$ arises from a maximal ideal in this way.
--
--   (11) For every $f \in C.\mathrm{integers}$ bounded on $C.\mathrm{dom}$ and every $Q \notin N$, the $C$-residue of $f$ lies in the valuation subring of $Q$.
--
--   (12) Every nonzero prime ideal of that intersection ring is maximal.
--
--   (13) For every $Q \notin N$ there are $\zeta$ and $\gamma \in \Gamma_0(M')$ and an $f \in C.\mathrm{integers}$, bounded on $C.\mathrm{dom}$, whose image under `levelAutBar q M' ζ γ` also lies in $C.\mathrm{integers}$, with $0 < Q.\mathrm{ord}$ of the $C$-residue of $f$ while $0 < Q.\mathrm{ord}$ fails for the $C$-residue of that image.
--
--   (14) Finally, there is a family $An$ of annuli $An_x :$ `Annulus A (fieldBar q M')` indexed by $x \in N$ — each consisting of a set $An_x.\mathrm{dom}$ of places of $\bar F$, a parameter $An_x.\mathrm{param} \in \bar F$ and a modulus in the maximal ideal of $A$, subject to the axioms of `Annulus` (rationality and integrality of the parameter with value in the maximal ideal and nonzero, the modulus factoring through each such value, a unique place of the domain for each admissible value of the parameter, order one for the parameter minus its value, and the unit principle for functions of order zero on the domain) — with the following four properties.
--
--   (14a) Attachment: for each $x \in N$, $An_x$ `IsAttached` to $C$ at $x$, that is, $x \in C.\mathrm{nodes}$, the parameter of $An_x$ lies in $C.\mathrm{integers}$ with $x.\mathrm{ord}$ of its $C$-residue equal to $1$, and for every $f \in C.\mathrm{integers}$ with nonzero $C$-residue and $P.\mathrm{ord}(f) = 0$ throughout $An_x.\mathrm{dom}$, and every $P \in An_x.\mathrm{dom}$, the element $P.\mathrm{evalAt}(f)\cdot (P.\mathrm{evalAt}\,An_x.\mathrm{param})^{-x.\mathrm{ord}(C\text{-residue of }f)}$ lies in $A$ and is a unit there.
--
--   (14b) Mobility: for each $x \in N$ there are $\zeta$ and $\gamma \in \Gamma_0(M')$ and some $x' \in N$ with $x' \neq x$ such that the domain of the pullback of $An_x$ along `levelAutBar q M' ζ γ` equals $An_{x'}.\mathrm{dom}$.
--
--   (14c) Separation: for every valuation subring $O$ of $\bar F$ and all $x, x' \in N$, if $O$ meets $\overline{\mathbb{Q}}$ exactly in $A$ (an element of $\overline{\mathbb{Q}}$ has its image in $O$ precisely when it lies in $A$), if there is $t \in O$ such that $t - a$ lies in $O$ and is a unit of $O$ for every $a \in A$, if $O$ fails to contain all elements of $\bar F$ bounded on $C.\mathrm{dom}$, and if $O$ contains all elements bounded on $An_x.\mathrm{dom}$ and also all elements bounded on $An_{x'}.\mathrm{dom}$, then $x = x'$.
--
--   (14d) Type-II exhaustion in charted form: for every field $F_o$ with a $\kappa$-algebra structure which is a curve over $\kappa$ in the sense of `IsCurveOver` (principal divisors of degree zero exist, residue fields of places are finite over $\kappa$, and the module of Kähler differentials is free of rank one) and is essentially of finite type over $\kappa$, and for every component chart $C_o :$ `ComponentChart A (fieldBar q M') Fo`, the following implication holds. Suppose $C_o$ is centred over $s$, in the sense that for every $f \in R_0.\mathrm{integers}$ satisfying the two conditions of (2) — regularity at all places of $F_{\mathrm{full}}$ where $J$ is regular, and $R_0$-residue in the valuation subring of $s$ — the image of $f$ in $\bar F$ lies in $C_o.\mathrm{integers}$, and moreover for every $a \in A$ with $\mathrm{res}_A(a) = s.\mathrm{evalAt}$ of the $R_0$-residue of $f$, the difference of that image and $a$ lies in $C_o.\mathrm{integers}$ and in fact in the maximal ideal of $C_o.\mathrm{integers}$. Then either $C_o.\mathrm{integers}$ contains every element of $\bar F$ bounded on $C.\mathrm{dom}$, or there is $x \in N$ such that $C_o.\mathrm{integers}$ contains every element bounded on $An_x.\mathrm{dom}$.
--
--   The quantification in (14d) over component charts with curve reduction, rather than over arbitrary valuation subrings of $\bar F$ centred over $s$, is what distinguishes this charted form of the exhaustion clause.
--
--   This is the local description, at a place of $\overline{\mathbb{Q}}$ above $q = 2$ and over a supersingular point $s$ of the reduction, of the semistable geometry of the modular curve of level $\Gamma(q) \cap \Gamma_0(M')$ (realised here through $X_H$ of level $q^2M'$ with $H$ the units congruent to $1$ modulo $q$): a component chart with $q+1$ exceptional places, residue discs on which $j$ is integral, the affinoid ring of the component and the annuli attached at the exceptional places, invariance under the level automorphisms for $\Gamma_0(M')$, and an exhaustion clause saying that every component chart with curve reduction centred over $s$ dominates either the component or one of the annuli. The auxiliary prime $\ell \equiv 11 \pmod{12}$ dividing $M'$ rigidifies the level. It is used by [`ModularCurve.FullLevel.componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq_of_eq_two_of_dvd) to identify the Gauss ring of a level-invariant chart over a supersingular point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_supersingularChart_local_affinoid_nodeAnnuli_charted_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.exists_supersingularChart_local_affinoid_nodeAnnuli_charted_of_eq_two_of_dvd
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
