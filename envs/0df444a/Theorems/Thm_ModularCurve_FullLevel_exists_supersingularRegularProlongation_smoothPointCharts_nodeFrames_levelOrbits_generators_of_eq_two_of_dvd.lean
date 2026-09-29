-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodeFrames_levelOrbits_generators_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodeFrames_levelOrbits_generators_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/d5113857-c719-51f4-b4ab-3b0de65e874d
-- title:
--   Supersingular chart data and Drinfeld identification at q=2
-- statement:
--   Fix a prime $q$ together with the hypothesis `hq2 : q = 2`, a nonzero natural number $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ dividing $M'$ (the rigidifying auxiliary prime). Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with `hA : A.LiesOverPrime q`, i.e. $q$ is a non-unit of $A$, and write $\kappa =$ `ResidueField A`.
--
--   Three fields of Laurent series are in play. `modularFunctionFieldC κ M'` is the subfield of $\kappa((t))$ generated over $\kappa$ by the expansion `jqModC κ` of $j$ and by its $M'$-fold substitution `jqNModC κ M'`; `modularFunctionFieldBar M'` is the subfield of $\overline{\mathbb{Q}}((t))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the full level-$M'$ modular function field `modularFunctionFieldFull M'`; and `fieldBar q M'` is the subfield of $\overline{\mathbb{Q}}((t))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of `xHFunctionField (q^2*M') (levelH q M')`, where `levelH q M'` is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, that is, the group of units congruent to $1$ modulo $q$. Throughout, a `Place K F` is a valuation subring of $F$ containing the image of $K$, distinct from $F$, whose ring is a principal ideal ring; `P.ord f` is minus the logarithm of the associated $\mathbb{Z}^{m0}$-valuation of $f$, `P.IsRational` says that $K \to$ `P.ResidueField` is surjective, and `P.evalAt f` is the element of $K$ corresponding to the residue of $f$ when $f$ lies in the valuation ring, and $0$ otherwise.
--
--   The remaining data are: a finite set $W$ of places of `modularFunctionFieldC κ M'` over $\kappa$, with the hypothesis `hW` that $W$ consists exactly of the supersingular places, namely the places $w$ that are rational, satisfy the predicate `IsAffineGeomPlace`, and have `w.evalAt (jGeomGen κ M') ∈ ssJSet q κ`; the inclusion `hle : modularFunctionFieldBar M' ≤ fieldBar q M'`; a constant reduction $R_0$ of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'`, i.e. a valuation subring `R₀.integers` whose elements lying over $A$ are exactly those coming from $A$, together with a surjective residue homomorphism onto `modularFunctionFieldC κ M'` with kernel the maximal ideal, compatible with the residue map of $A$ on constants, a rescaling property, and a map on places preserving degrees and compatible with divisors; the hypothesis `hR₀`, which states that for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb{Q}}((t))$ lies in `modularFunctionFieldBar M'`, that element belongs to `R₀.integers` and its $R_0$-residue is, as a Laurent series over $\kappa$, the coefficientwise reduction of $y$ modulo the maximal ideal of $A$; and finally an element $s$ of $W$, a chosen supersingular place.
--
--   Write $\bar{j}$ for the element of `modularFunctionFieldBar M'` given by the coefficientwise image `coeffEmb (AlgebraicClosure ℚ) jq` of the $q$-expansion of $j$, and say that an element $f$ of `modularFunctionFieldBar M'` is *$j$-regular* if $0 \le P.\mathrm{ord}(f)$ for every place $P$ of `modularFunctionFieldBar M'` over $\overline{\mathbb{Q}}$ with $0 \le P.\mathrm{ord}(\bar{j})$.
--
--   The assertion is that there exist a field $FSS$, an algebra structure on $FSS$ over $\kappa$, and a regular prolongation $R$ of $A$ from `fieldBar q M'` to $FSS$ — a valuation subring `R.integers` of `fieldBar q M'` whose intersection with the constants is $A$, with a surjective residue homomorphism onto $FSS$ whose kernel is the maximal ideal, compatible with the residue map of $A$ on constants and satisfying the rescaling property — such that all of the following hold.
--
--   (1) $FSS$ contains an element transcendental over $\kappa$.
--
--   (2) (Reduction over $s$.) For every $f \in$ `R₀.integers` which is $j$-regular and whose $R_0$-residue lies in the valuation subring of the place $s$, the image of $f$ in `fieldBar q M'` under the inclusion `hle` lies in `R.integers`, and its $R$-residue is the image in $FSS$ of $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$.
--
--   (3) (Level invariance.) For every primitive $q$-th root of unity $\zeta$ in $\overline{\mathbb{Q}}$ (an element of `Idx q`) and every $\gamma \in \Gamma_0(M') \subseteq \mathrm{SL}_2(\mathbb{Z})$, the preimage of `R.integers` under the $\overline{\mathbb{Q}}$-automorphism `levelAutBar q M' ζ γ` of `fieldBar q M'` equals `R.integers`. Here `levelAutBar q M' ζ γ` is the automorphism obtained by choosing one whose effect on quotients of integral $q$-expansions of modular forms of level $\Gamma_H(q^2M')$ matches the slash action of `conjElem q γ` under any embedding $\overline{\mathbb{Q}} \to \mathbb{C}$ sending $\zeta$ to $e^{2\pi i/q}$, the identity being taken if no such automorphism exists.
--
--   (4) There exist a finite set $N$ of places of $FSS$ over $\kappa$, an assignment $Q \mapsto S_Q$ of subrings of `fieldBar q M'`, an assignment $Q \mapsto \varphi_Q$ of ring homomorphisms $A[X] \to S_Q$, an assignment $Q \mapsto \chi_{0,Q}$ of ring homomorphisms $S_Q \to \kappa$, and an assignment $Q \mapsto D_Q$ of sets of places of `fieldBar q M'` over $\overline{\mathbb{Q}}$, subject to the following conjuncts.
--
--   (4a) $N$ has exactly $q+1$ elements.
--
--   (4b) (Smooth-point charts.) For every place $Q \notin N$: every $a \in A$, viewed as a constant, lies in $S_Q$; $\varphi_Q$ is formally smooth and formally unramified; $\varphi_Q(C\,a)$ is the constant $a$ in `fieldBar q M'`, and $\chi_{0,Q}(\varphi_Q(C\,a))$ is the residue of $a$ in $\kappa$; $\chi_{0,Q}(\varphi_Q(X)) = 0$; for every $c \in A$ with residue $0$ there is exactly one ring homomorphism $\chi : S_Q \to A$ with $\chi(\varphi_Q(C\,a)) = a$ for all $a \in A$, with $\chi$ followed by the residue map of $A$ equal to $\chi_{0,Q}$, and with $\chi(\varphi_Q(X)) = c$; every $f \in S_Q$ lies in `R.integers`, its $R$-residue lies in the valuation subring of $Q$, and the residue of the latter in `Q.ResidueField` is the image of $\chi_{0,Q}(f)$; $\varphi_Q(X)$ lies in `R.integers` and $Q.\mathrm{ord}$ of its $R$-residue is $1$; the set $D_Q$ consists exactly of the rational places $P$ such that every $f \in S_Q$ lies in the valuation subring of $P$ with $P.\mathrm{evalAt}(f) \in A$, and such that for every $f \in S_Q$ the $A$-valuation of $P.\mathrm{evalAt}(f)$ is $< 1$ if and only if $\chi_{0,Q}(f) = 0$; for every ring homomorphism $\chi : S_Q \to A$ fixing the constants and reducing to $\chi_{0,Q}$ there is exactly one place $P \in D_Q$ with $P.\mathrm{evalAt}(f) = \chi(f)$ for all $f \in S_Q$; for $P \in D_Q$ an element $f$ of `fieldBar q M'` lies in the valuation subring of $P$ if and only if $f h = g$ for some $g, h \in S_Q$ with $P.\mathrm{evalAt}(h) \neq 0$; every nonzero $f$ with $P.\mathrm{ord}(f) = 0$ for all $P \in D_Q$ becomes a unit of $S_Q$ after multiplication by a nonzero constant $c \in \overline{\mathbb{Q}}$; and every $f \in$ `R.integers` lying in the valuation subring of every $P \in D_Q$ lies in $S_Q$.
--
--   (4c) (Disjointness of the discs.) For $Q, Q' \notin N$, if some place $P$ lies in both $D_Q$ and $D_{Q'}$, then $Q = Q'$.
--
--   (4d) (No cusps in the discs.) For $Q \notin N$ and $P \in D_Q$, $0 \le P.\mathrm{ord}$ of the image of $\bar{j}$ in `fieldBar q M'`.
--
--   (4e) (Level equivariance of $N$ and of the discs.) For every $\tau$ in the subgroup of $\overline{\mathbb{Q}}$-automorphisms of `fieldBar q M'` generated by the automorphisms `levelAutBar q M' ζ γ` with $\zeta \in$ `Idx q` and $\gamma \in \Gamma_0(M')$, and every proof that $\tau$ preserves `R.integers`, the induced residue automorphism `R.resAut τ` of $FSS$ over $\kappa$ satisfies: a place $Q$ lies in $N$ if and only if its translate does; and for $Q \notin N$ the translate $\{P : \tau^{-1} \cdot P \in D_Q\}$ of $D_Q$ equals $D_{\text{translate of }Q}$.
--
--   (4f) (Drinfeld identification, with level action.) For every algebra structure of $\mathbb{F}_{q^2} =$ `GaloisField q 2` on $\kappa$, every hypothesis that [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain, and every $\zeta \in$ `Idx q`, there are a subgroup $C_s$ of the group of $(q+1)$-st roots of unity of $\mathbb{F}_{q^2}$ and an isomorphism $e$ of $\kappa$-algebras from $FSS$ onto [`DrinfeldCurve.quotField q κ Cs`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32), the fixed field inside the Drinfeld function field of the subgroup generated by the actions of the elements $(1,\zeta')$ with $\zeta' \in C_s$, such that the cardinality of $C_s$ equals `placeWidthChar q M' s`, which is `jWidthChar q (s.evalAt (jGeomGen κ M'))` divided by `placeRamificationJ M' s` (for $q = 2$ the numerator is $12$ if the $j$-value at $s$ is $0$ and $1$ otherwise); and such that for every $\gamma \in \Gamma_0(M')$, every proof that `levelAutBar q M' ζ γ⁻¹` preserves `R.integers`, and every proof that $(\mathrm{redQ}\,q\,\gamma, 1)$ lies in the subgroup [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276), the automorphism of $FSS$ induced on residues by `levelAutBar q M' ζ γ⁻¹` corresponds under $e$ to the action of $(\mathrm{redQ}\,q\,\gamma, 1)$ through [`DrinfeldCurve.hFunctionFieldAction q κ`](def/DrinfeldCurve_FunctionField.html#L16) on the Drinfeld function field.
--
--   (4g) (Semilinear functoriality of the charts.) Let $g$ be a semilinear automorphism of `fieldBar q M'` over $\overline{\mathbb{Q}}$, i.e. a pair consisting of a ring automorphism of `fieldBar q M'` and a ring automorphism `SemilinearAut.baseAut g` of $\overline{\mathbb{Q}}$ intertwined by the structure map, such that the base automorphism preserves $A$, $g$ preserves `R.integers`, and $g$ fixes the image of $\bar{j}$. Let $\psi$ be a ring automorphism of $\kappa$ compatible with $g$ via the residue map of $A$, and $\varphi$ a ring automorphism of $FSS$ with $R.\mathrm{residue}(g \cdot f) = \varphi(R.\mathrm{residue}(f))$ for all $f \in$ `R.integers`. Then for all places $Q \notin N$ and $Q'$ of $FSS$ such that $y$ lies in the valuation subring of $Q'$ exactly when $\varphi^{-1}(y)$ lies in that of $Q$: $Q' \notin N$; $f \in S_Q$ if and only if $g \cdot f \in S_{Q'}$; $\chi_{0,Q'}(g \cdot f) = \psi(\chi_{0,Q}(f))$ for $f \in S_Q$; and $P \in D_Q$ if and only if $g \cdot P \in D_{Q'}$.
--
--   (4h) (Transitivity on $N$.) For all $x, x' \in N$ there are $\zeta \in$ `Idx q` and $\gamma \in \Gamma_0(M')$ such that `levelAutBar q M' ζ γ` preserves `R.integers` and its residue automorphism carries $x$ to $x'$.
--
--   (4i) For every $Q \notin N$ there are $\zeta \in$ `Idx q` and $\gamma \in \Gamma_0(M')$ such that `levelAutBar q M' ζ γ` preserves `R.integers` and its residue automorphism moves $Q$.
--
--   (4j) (Generators.) There are $n \in \mathbb{N}$ and elements $g_0, \dots, g_{n-1}$ of `R.integers` such that each $g_i$ lies in the valuation subring of every $P \in D_Q$ with $Q \notin N$, with $P.\mathrm{evalAt}(g_i) \in A$; and every $f \in FSS$ lying in the valuation subring of every place $Q \notin N$ belongs to the $\kappa$-subalgebra of $FSS$ generated by the residues $R.\mathrm{residue}(g_i)$.
--
--   (4k) (Node annuli and the covering property.) There is an assignment $x \mapsto \mathrm{An}(x)$ of annuli over $A$ in `fieldBar q M'` — each consisting of a set of places, a parameter, and a modulus in the maximal ideal of $A$, subject to the conditions of the structure `Annulus`: places in the domain are rational, the parameter has value in the maximal ideal of $A$ and nonzero there, the modulus is the value of the parameter times an element of the maximal ideal, each admissible value is attained at exactly one place of the domain, $P.\mathrm{ord}$ of the parameter minus its value is $1$, and the unit principle holds — such that:
--
--   for every $x \in N$: the parameter of $\mathrm{An}(x)$ lies in `R.integers` with $x.\mathrm{ord}$ of its $R$-residue equal to $1$, and for every $f \in$ `R.integers` with nonzero $R$-residue and $P.\mathrm{ord}(f) = 0$ for all $P$ in the domain of $\mathrm{An}(x)$, at each such $P$ the element $P.\mathrm{evalAt}(f) \cdot P.\mathrm{evalAt}(\text{param})^{-x.\mathrm{ord}(R.\mathrm{residue}(f))}$ lies in $A$ and is a unit there; the modulus of $\mathrm{An}(x)$ is nonzero in $\overline{\mathbb{Q}}$; no place of the domain of $\mathrm{An}(x)$ lies in any $D_Q$ with $Q \notin N$; and every place $P$ in the domain of $\mathrm{An}(x)$ reduces to $s$ in the following sense: for every $f \in$ `R₀.integers` which is $j$-regular and whose $R_0$-residue lies in the valuation subring of $s$, and every $a \in A$ whose residue equals $s.\mathrm{evalAt}$ of that $R_0$-residue, the difference $P.\mathrm{evalAt}(f) - a$ lies in $A$ and in its maximal ideal;
--
--   the annuli are pairwise disjoint: for $x, x' \in N$, if a place lies in the domains of both $\mathrm{An}(x)$ and $\mathrm{An}(x')$ then $x = x'$;
--
--   the annuli are level-equivariant: for every $\tau$ in the subgroup generated by the automorphisms `levelAutBar q M' ζ γ` with $\zeta \in$ `Idx q`, $\gamma \in \Gamma_0(M')$, every proof that $\tau$ preserves `R.integers`, and every $x \in N$, the translate $\{P : \tau^{-1} \cdot P \in \mathrm{An}(x).\mathrm{dom}\}$ equals the domain of $\mathrm{An}$ at the translate of $x$ by the residue automorphism of $\tau$;
--
--   and the covering property holds: every rational place $P$ of `fieldBar q M'` over $\overline{\mathbb{Q}}$ which reduces to $s$ in the sense just described lies either in $D_Q$ for some $Q \notin N$ or in the domain of $\mathrm{An}(x)$ for some $x \in N$.
--
--   This is the $q = 2$, rigid-auxiliary-level instance of the construction, over a valuation subring $A$ of $\overline{\mathbb{Q}}$ above $q$ and over a chosen supersingular place $s$ of the level-$M'$ modular function field in characteristic $q$, of the semistable chart data for the function field of the curve of level $\Gamma_H(q^2M')$ with $H$ the units congruent to $1$ modulo $q$: the $q+1$ ends of the supersingular affinoid, the smooth-point charts with their residue discs, the node annuli, algebra generators for the reduced field, the level-equivariance of all of these, and the identification of the reduced field with a quotient of the Drinfeld curve $xy^q - x^q y = 1$ compatible with the $\Gamma_0(M')$-action. It is obtained from the companion statement [`ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_inertia_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_inertia_of_eq_two_of_dvd), which assumes in addition an element $\pi \in A$ with $\pi^{q^2-1} = q$, and it is used by [`ModularCurve.FullLevel.exists_algEquiv_quotField_of_chart_over_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.exists_algEquiv_quotField_of_chart_over_of_eq_two_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodeFrames_levelOrbits_generators_of_eq_two_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_PlaceWidthChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open AlgebraicCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodeFrames_levelOrbits_generators_of_eq_two_of_dvd
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
      (R : RegularProlongation A (fieldBar q M') FSS),
      (∃ t : FSS, Transcendental (ResidueField A) t) ∧
      (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers,
            R.residue ⟨_, hC⟩ = algebraMap (ResidueField A) FSS
              ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
                (R₀.residue ⟨f, hf⟩))) ∧
      (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
        R.integers.comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom = R.integers) ∧
      ∃ (N : Finset (Place (ResidueField ↥A) FSS))
        (Sx : Place (ResidueField ↥A) FSS → Subring ↥(fieldBar q M'))
        (φx : (Q : Place (ResidueField ↥A) FSS) → (Polynomial ↥A →+* ↥(Sx Q)))
        (χ₀x : (Q : Place (ResidueField ↥A) FSS) → (↥(Sx Q) →+* ResidueField ↥A))
        (Dx : Place (ResidueField ↥A) FSS → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
        N.card = q + 1 ∧
        (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →

          (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ Sx Q) ∧
          (φx Q).FormallySmooth ∧ (φx Q).FormallyUnramified ∧
          (∀ a : ↥A, ((φx Q (Polynomial.C a) : ↥(Sx Q)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ))) ∧
          (∀ a : ↥A, χ₀x Q (φx Q (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
          χ₀x Q (φx Q Polynomial.X) = 0 ∧
          (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
            ∃! χ : ↥(Sx Q) →+* ↥A, (∀ a : ↥A, χ (φx Q (Polynomial.C a)) = a) ∧
              (∀ f : ↥(Sx Q), IsLocalRing.residue ↥A (χ f) = χ₀x Q f) ∧ χ (φx Q Polynomial.X) = c) ∧
          (∀ f : ↥(Sx Q), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
            IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
              algebraMap (ResidueField ↥A) Q.ResidueField (χ₀x Q f)) ∧
          (∃ hR : ((φx Q Polynomial.X : ↥(Sx Q)) : ↥(fieldBar q M')) ∈ R.integers,
            Q.ord (R.residue ⟨((φx Q Polynomial.X : ↥(Sx Q)) : ↥(fieldBar q M')), hR⟩) = 1) ∧
          (∀ P, P ∈ Dx Q ↔ (P.IsRational ∧ (∀ f : ↥(Sx Q), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
            (∀ f : ↥(Sx Q), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χ₀x Q f = 0))) ∧
          (∀ χ : ↥(Sx Q) →+* ↥A, (∀ a : ↥A, χ (φx Q (Polynomial.C a)) = a) →
            (∀ f : ↥(Sx Q), IsLocalRing.residue ↥A (χ f) = χ₀x Q f) →
            ∃! P, P ∈ Dx Q ∧ ∀ f : ↥(Sx Q), P.evalAt (f : ↥(fieldBar q M')) = ((χ f : ↥A) : (AlgebraicClosure ℚ))) ∧
          (∀ P ∈ Dx Q, ∀ f : ↥(fieldBar q M'), f ∈ P.toValuationSubring ↔
            ∃ g h : ↥(Sx Q), P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧
          (∀ f : ↥(fieldBar q M'), f ≠ 0 → (∀ P ∈ Dx Q, P.ord f = 0) →
            ∃ (c : (AlgebraicClosure ℚ)) (u : (↥(Sx Q))ˣ), c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * f = ((u : ↥(Sx Q)) : ↥(fieldBar q M'))) ∧
          (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ Dx Q, f ∈ P.toValuationSubring) → f ∈ Sx Q)) ∧

        (∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N → Q' ∉ N → ∀ P, P ∈ Dx Q → P ∈ Dx Q' → Q = Q') ∧

        (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P ∈ Dx Q, 0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : fieldBar q M')) ∧

        (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
            ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
          ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
            (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N) ∧
            (Q ∉ N → AlgebraicCurve.RegularProlongation.smulDisc τ (Dx Q) = Dx (R.resAut τ hτ • Q))) ∧

        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∀ (ζ : Idx q),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
            (e : FSS ≃ₐ[ResidueField ↥A] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
            Nat.card Cs = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
              ∀ (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ⁻¹ f ∈ R.integers ↔ f ∈ R.integers)
                (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
                ∀ x : FSS,
                  ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                    DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) ∧

        (∀ (g : SemilinearAut (AlgebraicClosure ℚ) ↥(fieldBar q M'))
          (hgA : ∀ x : AlgebraicClosure ℚ, SemilinearAut.baseAut g x ∈ A ↔ x ∈ A)
          (hgR : ∀ f : ↥(fieldBar q M'), g • f ∈ R.integers ↔ f ∈ R.integers)
          (hgj : g • (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) =
            IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')))
          (ψ : ResidueField ↥A ≃+* ResidueField ↥A)
          (hψ : ∀ a : ↥A, ψ (IsLocalRing.residue ↥A a) =
            IsLocalRing.residue ↥A ⟨SemilinearAut.baseAut g (a : AlgebraicClosure ℚ), (hgA (a : AlgebraicClosure ℚ)).mpr a.2⟩)
          (φ : FSS ≃+* FSS)
          (hφ : ∀ (f : ↥(fieldBar q M')) (hf : f ∈ R.integers),
            R.residue ⟨g • f, (hgR f).mpr hf⟩ = φ (R.residue ⟨f, hf⟩)),
          ∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N →
            (∀ y : FSS, y ∈ Q'.toValuationSubring ↔ φ.symm y ∈ Q.toValuationSubring) →
            Q' ∉ N ∧
            ∃ hS : ∀ f : ↥(fieldBar q M'), f ∈ Sx Q ↔ g • f ∈ Sx Q',
              (∀ f : ↥(Sx Q), χ₀x Q' ⟨g • (f : ↥(fieldBar q M')), (hS (f : ↥(fieldBar q M'))).mp f.2⟩ = ψ (χ₀x Q f)) ∧
              (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ Dx Q ↔ g • P ∈ Dx Q')) ∧

        (∀ x x' : Place (ResidueField ↥A) FSS, x ∈ N → x' ∈ N →
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)) (_ : γ ∈ Gamma0 M')
            (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ f ∈ R.integers ↔ f ∈ R.integers),
            R.resAut (levelAutBar q M' ζ γ) hτ • x = x') ∧

        (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)) (_ : γ ∈ Gamma0 M')
            (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ f ∈ R.integers ↔ f ∈ R.integers),
            R.resAut (levelAutBar q M' ζ γ) hτ • Q ≠ Q) ∧

        (∃ (n : ℕ) (g : Fin n → ↥(fieldBar q M')) (hg : ∀ i, g i ∈ R.integers),
          (∀ i, ∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P ∈ Dx Q,
            g i ∈ P.toValuationSubring ∧ P.evalAt (g i) ∈ A) ∧
          ∀ f : FSS, (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → f ∈ Q.toValuationSubring) →
            f ∈ Algebra.adjoin (ResidueField ↥A) (Set.range fun i => R.residue ⟨g i, hg i⟩)) ∧

        (∃ An : Place (ResidueField ↥A) FSS → Annulus A ↥(fieldBar q M'),
          (∀ x ∈ N,
            (∃ hz : (An x).param ∈ R.integers, x.ord (R.residue ⟨(An x).param, hz⟩) = 1 ∧
              ∀ (f : ↥(fieldBar q M')) (hf : f ∈ R.integers), R.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ (An x).dom, P.ord f = 0) →
                ∀ P ∈ (An x).dom,
                  ∃ h : P.evalAt f * (P.evalAt (An x).param) ^ (-(x.ord (R.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
            ((An x).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
            (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P, P ∈ (An x).dom → P ∉ Dx Q) ∧
            (∀ P ∈ (An x).dom, (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
                (∀ P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                  0 ≤ P'.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P'.ord (f : ↥(modularFunctionFieldBar M'))) →
                (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                  ∀ a : A, IsLocalRing.residue A a =
                      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                    ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                      (⟨_, h⟩ : A) ∈ IsLocalRing.maximalIdeal A))) ∧
          (∀ x x' : Place (ResidueField ↥A) FSS, x ∈ N → x' ∈ N → ∀ P, P ∈ (An x).dom → P ∈ (An x').dom → x = x') ∧
          (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
              ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers), ∀ x ∈ N,
              AlgebraicCurve.RegularProlongation.smulDisc τ (An x).dom = (An (R.resAut τ hτ • x)).dom) ∧

          (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational →
            (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
              (∀ P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                0 ≤ P'.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                  ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P'.ord (f : ↥(modularFunctionFieldBar M'))) →
              (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                  (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                ∀ a : A, IsLocalRing.residue A a =
                    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                  ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                    (⟨_, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) →
            (∃ Q, Q ∉ N ∧ P ∈ Dx Q) ∨ ∃ x, x ∈ N ∧ P ∈ (An x).dom)) := by sorry
