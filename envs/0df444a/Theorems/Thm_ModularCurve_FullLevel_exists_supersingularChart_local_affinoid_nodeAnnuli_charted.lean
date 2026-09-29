-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_supersingularChart_local_affinoid_nodeAnnuli_charted
-- name    : ModularCurve.FullLevel.exists_supersingularChart_local_affinoid_nodeAnnuli_charted
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/53e25ea3-110e-579d-9136-fa09b59c1176
-- title:
--   Supersingular component chart with node annuli, charted exhaustion
-- statement:
--   Fix a prime $q$ with $q \ge 5$ and a natural number $M' \neq 0$ with $q \nmid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime q`, i.e. $q$ is a nonunit of $A$; write $\kappa =$ `ResidueField A`. Places here are in the sense of the project: a place of a field extension $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$, whose valuation ring is a principal ideal ring; `P.ord` is the associated normalised integer valuation, `P.evalAt f` the value in $K$ of $f$ at $P$ (defined via the inverse of $K \to$ `P.ResidueField`, and $0$ if $f \notin$ `P.toValuationSubring`), and `P.IsRational` says that $K \to$ `P.ResidueField` is surjective.
--
--   The data of the hypotheses are as follows. A finite set $W$ of places of `modularFunctionFieldC κ M'` over $\kappa$ is given, together with `hW`, which says that $W$ consists exactly of the supersingular places `ssPlaces q M' κ`: those places $w$ that are rational, are affine geometric places, and satisfy $w(\,$`jGeomGen κ M'`$\,) \in$ `ssJSet q κ`. The hypothesis `hle` is the inclusion of intermediate fields $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ inside `LaurentSeries (AlgebraicClosure ℚ)` over $\overline{\mathbb{Q}}$, the first being the base change to $\overline{\mathbb{Q}}$ of the full level-$M'$ modular function field, the second the base change of the function field of the $X_H$ of level $q^2M'$ for $H =$ `levelH q M'`, the kernel of the reduction `ZMod.unitsMap (dvd_sq_mul q M')` on $(\mathbb{Z}/q^2M')^\times$. Further, $R_0$ is a `ConstantReduction` of $A$ on $\mathrm{modularFunctionFieldBar}\,M'$ with reduced field `modularFunctionFieldC κ M'`: a valuation subring `R₀.integers`, a surjective ring homomorphism `R₀.residue` onto that reduced field with kernel the maximal ideal, a map on places preserving degrees and pushing forward principal divisors, compatibility with $A \hookrightarrow$ `R₀.integers` and reduction, and the scaling property that every nonzero element becomes, after multiplication by a suitable constant, an integer with nonzero residue. The hypothesis `hR₀` states that $R_0$ computes coefficientwise reduction: for every Laurent series $y$ with coefficients in $A$ whose image in `LaurentSeries (AlgebraicClosure ℚ)` lies in $\mathrm{modularFunctionFieldBar}\,M'$, that element lies in `R₀.integers` and its $R_0$-residue, read as a Laurent series over $\kappa$, is the series obtained from $y$ by reducing coefficients modulo the maximal ideal of $A$. Finally $s \in W$ is a chosen supersingular place. Throughout, $j$ denotes the element of $\mathrm{modularFunctionFieldBar}\,M'$ given by the image under `coeffEmb` of the $q$-expansion `jq` of the modular invariant.
--
--   The conclusion asserts the existence of a type `FSS`, a field structure and a $\kappa$-algebra structure on it, a `ComponentChart` $C$ for $A$ on $\mathrm{fieldBar}\,q\,M'$ with reduced field `FSS`, and a finite set $N$ of places of `FSS` over $\kappa$, such that all of the following hold. (Recall that a component chart consists of a valuation subring `C.integers`, a surjective residue homomorphism to the reduced field with kernel the maximal ideal, a set `C.dom` of places of the big field, a finite set `C.nodes` of places of the reduced field, a map `C.placeMap` sending `C.dom` off `C.nodes`, compatibility with $A$, the scaling property, the pointwise compatibility of residues with evaluation at places of `C.dom`, and pushforward of divisors supported on `C.dom` away from the nodes. Below, an element $f$ of $\mathrm{fieldBar}\,q\,M'$ is called *bounded on* `C.dom` when $f \in$ `P.toValuationSubring` and `P.evalAt f` $\in A$ for every $P \in$ `C.dom`, and similarly for the domains of annuli.)
--
--   (i) `FSS` contains an element transcendental over $\kappa$.
--
--   (ii) Centring at $s$: for every $f \in$ `R₀.integers` that is $j$-bounded, in the sense that $0 \le P.\mathrm{ord}(f)$ for every place $P$ of $\mathrm{modularFunctionFieldBar}\,M'$ over $\overline{\mathbb{Q}}$ with $0 \le P.\mathrm{ord}(j)$, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in `C.integers` and its $C$-residue is the image under $\kappa \to$ `FSS` of the value at $s$ of the $R_0$-residue of $f$.
--
--   (iii) Invariance of the integers: for every $\zeta \in$ `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$) and every $\gamma \in \Gamma_0(M') \subseteq \mathrm{SL}_2(\mathbb{Z})$, the integers of the pullback of $C$ along the automorphism `levelAutBar q M' ζ γ` coincide with `C.integers`.
--
--   (iv) $N$ has exactly $q+1$ elements.
--
--   (v) Residue discs away from $N$, with cusp-freeness: for every place $Q$ of `FSS` over $\kappa$ with $Q \notin N$ there is $T \in$ `C.integers` with nonzero $C$-residue, $Q.\mathrm{ord}$ of that residue equal to $1$, such that every $P \in$ `C.dom` with `C.placeMap P = Q` has $T$ in its valuation subring and `P.evalAt T` in the maximal ideal of $A$, and such that for every $c$ in the maximal ideal of $A$ there is exactly one place $P$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb{Q}}$ with $P \in$ `C.dom`, `C.placeMap P = Q` and `P.evalAt T` $= c$; moreover every $P \in$ `C.dom` with `C.placeMap P = Q` satisfies $0 \le P.\mathrm{ord}$ of the image of $j$ in $\mathrm{fieldBar}\,q\,M'$.
--
--   (vi) Invariance of the domain: for every $\zeta$ and every $\gamma \in \Gamma_0(M')$, the domain of the pullback of $C$ along `levelAutBar q M' ζ γ` equals `C.dom`.
--
--   (vii) The affinoid comparison, in two parts: every element of $\mathrm{fieldBar}\,q\,M'$ bounded on `C.dom` lies in `C.integers`; and every $g \in$ `FSS` lying in the valuation subring of every $Q \notin N$ is the $C$-residue of some element of `C.integers` bounded on `C.dom`.
--
--   (viii) Localisation: every $h \in$ `C.integers` admits $r$ and $s'$, both bounded on `C.dom`, with $s' \in$ `C.integers` of nonzero $C$-residue, such that $h\,s' = r$.
--
--   (ix) Every place in `C.dom` is rational.
--
--   (x) The place dictionary for the subring $S_N = \bigcap_{Q \notin N} Q.\mathrm{toValuationSubring}$ of `FSS`: every maximal ideal $\mathfrak m$ of $S_N$ determines a unique place $Q \notin N$ for which $\mathfrak m = \{g : g = 0 \text{ or } 0 < Q.\mathrm{ord}(g)\}$; and conversely every $Q \notin N$ arises from a maximal ideal of $S_N$ in this way.
--
--   (xi) For every $f \in$ `C.integers` bounded on `C.dom` and every $Q \notin N$, the $C$-residue of $f$ lies in the valuation subring of $Q$.
--
--   (xii) Every nonzero prime ideal of $S_N$ is maximal.
--
--   (xiii) For every $Q \notin N$ there are $\zeta$ and $\gamma \in \Gamma_0(M')$ and an element $f \in$ `C.integers`, bounded on `C.dom`, with `levelAutBar q M' ζ γ f` also in `C.integers`, such that $0 < Q.\mathrm{ord}$ of the $C$-residue of $f$ while $Q.\mathrm{ord}$ of the $C$-residue of the translate is not positive.
--
--   (xiv) Finally, a family of annuli $\mathrm{An} : N \to$ `Annulus A (fieldBar q M')` — each annulus consisting of a set of places, a parameter, a modulus in the maximal ideal of $A$, with the usual requirements: rationality of the places in the domain, the parameter having value in the maximal ideal of $A$, nonzero, with modulus divisible by that value; existence and uniqueness of a place in the domain with prescribed admissible parameter value; $\mathrm{ord}$ of the parameter minus its value equal to $1$; and the unit principle for functions of $\mathrm{ord}$ zero on the domain — subject to three conditions. (ATT) Each $\mathrm{An}\,x$ is attached to $C$ at $x$: $x \in$ `C.nodes`, the parameter of $\mathrm{An}\,x$ lies in `C.integers` with $x.\mathrm{ord}$ of its residue equal to $1$, and for every $f \in$ `C.integers` with nonzero residue and $\mathrm{ord}$ zero at all places of $\mathrm{An}\,x$, and every such place $P$, the element $P.\mathrm{evalAt}(f) \cdot (P.\mathrm{evalAt}(\text{param}))^{-x.\mathrm{ord}(C\text{-residue of } f)}$ lies in $A$ and is a unit there. (MOVE) For each $x \in N$ there are $\zeta$ and $\gamma \in \Gamma_0(M')$ and some $x' \in N$ with $x' \neq x$ such that the domain of the pullback of $\mathrm{An}\,x$ along `levelAutBar q M' ζ γ` equals the domain of $\mathrm{An}\,x'$. (SEP) For every valuation subring $O$ of $\mathrm{fieldBar}\,q\,M'$ and all $x, x' \in N$: if $O$ meets $\overline{\mathbb{Q}}$ exactly in $A$ (an element of $\overline{\mathbb{Q}}$ lies in $O$ if and only if it lies in $A$), if $O$ contains an element $t$ such that $t - a$ is a unit of $O$ for every $a \in A$, if $O$ does not contain all elements bounded on `C.dom`, and if $O$ does contain all elements bounded on the domain of $\mathrm{An}\,x$ and all elements bounded on the domain of $\mathrm{An}\,x'$, then $x = x'$.
--
--   (xv) The exhaustion clause, quantified over charts rather than over arbitrary valuation rings: for every type $F_o$ with a field structure and a $\kappa$-algebra structure such that $F_o$ is a curve over $\kappa$ in the sense of `IsCurveOver` (principal divisors of degree zero exist, all residue fields of places are finite over $\kappa$, and the module of Kähler differentials is free of rank one) and is essentially of finite type over $\kappa$, and for every component chart $C_o$ for $A$ on $\mathrm{fieldBar}\,q\,M'$ with reduced field $F_o$: if $C_o$ is centred at $s$, in the sense that for every $f \in$ `R₀.integers` which is $j$-bounded as in (ii) and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in `Co.integers` and, for every $a \in A$ whose residue in $\kappa$ equals the value at $s$ of the $R_0$-residue of $f$, the difference between that image and the image of $a$ lies in `Co.integers` and in the maximal ideal of `Co.integers`, then either every element bounded on `C.dom` lies in `Co.integers`, or there is $x \in N$ such that every element bounded on the domain of $\mathrm{An}\,x$ lies in `Co.integers`.
--
--   This is the construction of the supersingular part of the semistable reduction of the modular curve of level $\Gamma(q) \cap \Gamma_0(M')$ over a valuation ring $A \subseteq \overline{\mathbb{Q}}$ above $q$: a component chart over a chosen supersingular point $s$ of the level-$M'$ curve in characteristic $q$, with its affinoid ring of functions bounded on the associated residue discs, its $q+1$ exceptional places, and the annuli attached to them, permuted by the level automorphisms. It differs from the variant with unrestricted exhaustion in that the final clause classifies only those valuation rings that arise as the Gauss rings of component charts whose reduced field is a curve over the residue field of $A$; in this form it is used by [`ModularCurve.FullLevel.componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq`](thm.html#ModularCurve.FullLevel.componentChart_integers_eq_of_isCurveOver_of_over_of_comap_levelAutBar_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_supersingularChart_local_affinoid_nodeAnnuli_charted.lean

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

theorem ModularCurve.FullLevel.exists_supersingularChart_local_affinoid_nodeAnnuli_charted
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
