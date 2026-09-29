-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodeFrames_levelOrbits_generators_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodeFrames_levelOrbits_generators_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/5a0ec835-3d3a-5be7-b607-f44bf75cfb63
-- title:
--   Supersingular model at q=3: charts, node annuli, level orbits, generators
-- statement:
--   Throughout, $q$ is a prime with $q = 3$, $M'$ is a nonzero natural number not divisible by $q$, and $\ell$ is a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Further, $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `A.LiesOverPrime q`, i.e. $q$ is a nonunit of $A$; $\kappa =$ `ResidueField A` denotes its residue field. Here `modularFunctionFieldC κ M'` is the intermediate field of `LaurentSeries κ` generated over $\kappa$ by the reductions `jqModC κ` and `jqNModC κ M'` of the $q$-expansions of $j$ and $j_{M'}$; `modularFunctionFieldBar M'` is the intermediate field of `LaurentSeries (AlgebraicClosure ℚ)` obtained by adjoining to $\overline{\mathbb{Q}}$ the coefficientwise images of the full level-$M'$ modular function field `modularFunctionFieldFull M'`; and `fieldBar q M'` is `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')`, where `levelH q M'` is the kernel of a reduction map of unit groups of `ZMod (q ^ 2 * M')`. The element of `modularFunctionFieldBar M'` given by the coefficientwise image `coeffEmb (AlgebraicClosure ℚ) jq` of the $q$-expansion of $j$ is referred to below as $j$.
--
--   The remaining data are: a finset $W$ of places of `modularFunctionFieldC κ M'` over $\kappa$, with the hypothesis `hW` that $W$ is exactly `ssPlaces q M' κ`, that is, the set of places $w$ that are rational (the structure map $\kappa \to w$'s residue field is surjective), satisfy `IsAffineGeomPlace`, and have $w(\,$`jGeomGen`$\,) \in$ `ssJSet q κ`; the hypothesis `hle` that `modularFunctionFieldBar M'` is contained in `fieldBar q M'`; a constant reduction $R_0$ of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'` (a valuation subring $R_0.\mathrm{integers}$ with a surjective residue map onto `modularFunctionFieldC κ M'` whose kernel is the maximal ideal, inducing on constants the reduction $A \to \kappa$, together with a place map of the same degrees and the divisor-compatibility and scaling axioms of `ConstantReduction`); the hypothesis `hR₀`, that for every Laurent series $y$ with coefficients in $A$ whose image under `coeffMap A.subtype` lies in `modularFunctionFieldBar M'`, that image lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$; and an element $s \in W$, i.e. a supersingular place.
--
--   The assertion is that there exist a field $FSS$, an algebra structure of $\kappa$ on $FSS$, and a regular prolongation $R$ of $A$ from `fieldBar q M'` to $FSS$ (a valuation subring $R.\mathrm{integers}$ of `fieldBar q M'` meeting the constants in $A$, with a surjective residue map to $FSS$ whose kernel is the maximal ideal, inducing the reduction $A \to \kappa$ on constants, and such that every nonzero element of `fieldBar q M'` becomes, after multiplication by a constant, an element of $R.\mathrm{integers}$ with nonzero residue), such that the following hold.
--
--   (1) Some $t \in FSS$ is transcendental over $\kappa$.
--
--   (2) $R$ prolongs the specialisation given by $s$: for every $f \in R_0.\mathrm{integers}$ inside `modularFunctionFieldBar M'` which is regular wherever $j$ is (for every place $P$ of `modularFunctionFieldBar M'` over $\overline{\mathbb{Q}}$, $0 \le P.\mathrm{ord}\,(j)$ implies $0 \le P.\mathrm{ord}\,(f)$) and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in `fieldBar q M'` under the inclusion `hle` lies in $R.\mathrm{integers}$, and its $R$-residue is the image in $FSS$ of $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$.
--
--   (3) For every $\zeta$ in `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$) and every $\gamma \in SL(2,\mathbb{Z})$ lying in $\Gamma_0(M')$, the preimage of $R.\mathrm{integers}$ under `levelAutBar q M' ζ γ` is $R.\mathrm{integers}$.
--
--   (4) There exist a finset $N$ of places of $FSS$ over $\kappa$, and families, indexed by the places $Q$ of $FSS$ over $\kappa$, consisting of a subring $S_Q$ of `fieldBar q M'`, a ring homomorphism $\varphi_Q : A[X] \to S_Q$, a ring homomorphism $\chi^0_Q : S_Q \to \kappa$ and a set $D_Q$ of places of `fieldBar q M'` over $\overline{\mathbb{Q}}$, with the following properties.
--
--   The cardinality of $N$ is $q + 1$. For every $Q \notin N$: the image of each $a \in A$ under $\overline{\mathbb{Q}} \to$ `fieldBar q M'` lies in $S_Q$; $\varphi_Q$ is formally smooth and formally unramified; $\varphi_Q(C\,a)$ is that image of $a$, and $\chi^0_Q(\varphi_Q(C\,a))$ is the reduction of $a$ in $\kappa$; $\chi^0_Q(\varphi_Q(X)) = 0$; for every $c \in A$ with zero reduction there is exactly one ring homomorphism $\chi : S_Q \to A$ with $\chi(\varphi_Q(C\,a)) = a$ for all $a \in A$, with reduction of $\chi(f)$ equal to $\chi^0_Q(f)$ for all $f \in S_Q$, and with $\chi(\varphi_Q(X)) = c$; every $f \in S_Q$ lies in $R.\mathrm{integers}$, its $R$-residue lies in the valuation subring of $Q$, and the residue of the latter in $Q$'s residue field is the image of $\chi^0_Q(f)$ under $\kappa \to Q.\mathrm{ResidueField}$; $\varphi_Q(X)$ lies in $R.\mathrm{integers}$ and $Q.\mathrm{ord}$ of its $R$-residue is $1$; $D_Q$ consists precisely of those places $P$ of `fieldBar q M'` over $\overline{\mathbb{Q}}$ that are rational, satisfy $f \in P$'s valuation subring with $P.\mathrm{evalAt}(f) \in A$ for all $f \in S_Q$, and for which, for all $f \in S_Q$, the $A$-valuation of $P.\mathrm{evalAt}(f)$ is $< 1$ if and only if $\chi^0_Q(f) = 0$; every ring homomorphism $\chi : S_Q \to A$ that is the identity on the constants $\varphi_Q(C\,a)$ and reduces to $\chi^0_Q$ arises from exactly one $P \in D_Q$, in the sense that $P.\mathrm{evalAt}(f) = \chi(f)$ for all $f \in S_Q$; for $P \in D_Q$ the valuation subring of $P$ is the set of $f$ with $f\,h = g$ for some $g, h \in S_Q$ with $P.\mathrm{evalAt}(h) \neq 0$; every nonzero $f$ in `fieldBar q M'` with $P.\mathrm{ord}(f) = 0$ for all $P \in D_Q$ satisfies $c\,f = u$ for some nonzero constant $c \in \overline{\mathbb{Q}}$ and some unit $u$ of $S_Q$; and every $f \in R.\mathrm{integers}$ lying in the valuation subring of each $P \in D_Q$ lies in $S_Q$.
--
--   The discs are pairwise disjoint: if $Q, Q' \notin N$ and some $P$ lies in both $D_Q$ and $D_{Q'}$, then $Q = Q'$. They avoid the cusps in the sense that for $Q \notin N$ and $P \in D_Q$ one has $0 \le P.\mathrm{ord}$ of the image of $j$ in `fieldBar q M'`. They are permuted by the level automorphisms: for every $\tau$ in the subgroup of $\overline{\mathbb{Q}}$-automorphisms of `fieldBar q M'` generated by the elements `levelAutBar q M' ζ γ` with $\zeta$ in `Idx q` and $\gamma \in \Gamma_0(M')$, and every proof $h_\tau$ that $\tau$ preserves $R.\mathrm{integers}$, the induced automorphism $R.\mathrm{resAut}\,\tau\,h_\tau$ of $FSS$ over $\kappa$ satisfies: a place $Q$ lies in $N$ if and only if its translate does, and for $Q \notin N$ the translate $\{P \mid \tau^{-1} \cdot P \in D_Q\}$ of $D_Q$ is $D$ at the translated place.
--
--   Next, an identification of $FSS$ with a quotient of the Drinfeld curve: for every algebra structure of `GaloisField q 2` on $\kappa$, every witness that [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) (the quotient of $\kappa[x,y]$ by `drinfeldPoly q κ - 1`) is a domain, and every $\zeta$ in `Idx q`, there exist a subgroup $C_s$ of the $(q+1)$-st roots of unity of `GaloisField q 2` and an isomorphism $e$ of $\kappa$-algebras from $FSS$ onto [`DrinfeldCurve.quotField q κ Cs`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32), the fixed field in the Drinfeld function field of the subgroup generated by the actions of the elements $(1,\zeta')$, $\zeta' \in C_s$, such that the cardinality of $C_s$ equals $2\,$`placeWidthChar q M' s`, and such that for every $\gamma \in \Gamma_0(M')$, every witness that `levelAutBar q M' ζ γ⁻¹` preserves $R.\mathrm{integers}$ and every witness that $(\,$`redQ q γ`$, 1)$ lies in [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276) (the kernel of the character given by the determinant composed with $\mathbb{Z}/q \to \mathbb{F}_{q^2}$ times the $(q+1)$-st power on the second factor), $e$ intertwines the induced residue automorphism of $FSS$ attached to `levelAutBar q M' ζ γ⁻¹` with the action `hFunctionFieldAction q κ` of $(\,$`redQ q γ`$, 1)$ on the Drinfeld function field.
--
--   Next, semilinear (Galois) equivariance of the whole package: for every semilinear automorphism $g$ of `fieldBar q M'` over $\overline{\mathbb{Q}}$ (a pair consisting of a ring automorphism of `fieldBar q M'` and one of $\overline{\mathbb{Q}}$, compatible with the structure map), subject to the hypotheses that `baseAut g` preserves $A$ ($h_{gA}$), that $g$ preserves $R.\mathrm{integers}$ ($h_{gR}$) and that $g$ fixes the image of $j$ in `fieldBar q M'` ($h_{gj}$), and for every ring automorphism $\psi$ of $\kappa$ compatible with `baseAut g` on reductions of elements of $A$ ($h_\psi$) and every ring automorphism $\varphi$ of $FSS$ with $R.\mathrm{residue}(g \cdot f) = \varphi(R.\mathrm{residue}(f))$ for all $f \in R.\mathrm{integers}$ ($h_\varphi$): for all places $Q, Q'$ of $FSS$ over $\kappa$ with $Q \notin N$ and with $Q'$ the transport of $Q$ along $\varphi$ (i.e. $y$ lies in the valuation subring of $Q'$ if and only if $\varphi^{-1}(y)$ lies in that of $Q$), one has $Q' \notin N$, and, granted that $f \in S_Q$ holds if and only if $g \cdot f \in S_{Q'}$, one has $\chi^0_{Q'}(g \cdot f) = \psi(\chi^0_Q(f))$ for all $f \in S_Q$, and $P \in D_Q$ if and only if $g \cdot P \in D_{Q'}$ for every place $P$ of `fieldBar q M'` over $\overline{\mathbb{Q}}$.
--
--   Next, two orbit statements: the level automorphisms act transitively on $N$, in the sense that for all $x, x' \in N$ there are $\zeta$ in `Idx q`, $\gamma \in \Gamma_0(M')$ and a witness that `levelAutBar q M' ζ γ` preserves $R.\mathrm{integers}$ for which the induced automorphism carries $x$ to $x'$; and for every $Q \notin N$ there are $\zeta$, $\gamma \in \Gamma_0(M')$ and such a witness for which the induced automorphism moves $Q$.
--
--   Next, generators: there exist $n \in \mathbb{N}$ and $g_0, \dots, g_{n-1}$ in $R.\mathrm{integers}$ such that each $g_i$ lies in the valuation subring of every $P \in D_Q$ with $Q \notin N$ and has $P.\mathrm{evalAt}(g_i) \in A$ there, and such that every $f \in FSS$ lying in the valuation subring of every $Q \notin N$ lies in the $\kappa$-subalgebra of $FSS$ generated by the $R$-residues of the $g_i$.
--
--   Finally, node annuli: there exists an assignment $x \mapsto \mathrm{An}(x)$ of an `Annulus A (fieldBar q M')` to each place of $FSS$ over $\kappa$ — that is, a set of places together with a parameter and a modulus in the maximal ideal of $A$, subject to the annulus axioms: at each place of the domain the parameter has nonzero value in the maximal ideal of $A$ through which the modulus factors, each admissible value is attained at exactly one place of the domain, the parameter minus its value has order $1$, and a function with no zeros or poles on the domain is a constant times a power of the parameter times a unit — such that: for each $x \in N$, the parameter of $\mathrm{An}(x)$ lies in $R.\mathrm{integers}$, $x.\mathrm{ord}$ of its $R$-residue is $1$, and for every $f \in R.\mathrm{integers}$ with nonzero $R$-residue and with $P.\mathrm{ord}(f) = 0$ for all $P$ in the domain of $\mathrm{An}(x)$, at each such $P$ the element $P.\mathrm{evalAt}(f)\cdot P.\mathrm{evalAt}(\mathrm{param})^{-x.\mathrm{ord}(R.\mathrm{residue}\,f)}$ lies in $A$ and is a unit there; the modulus of $\mathrm{An}(x)$ is nonzero in $\overline{\mathbb{Q}}$; no place of the domain of $\mathrm{An}(x)$ lies in any $D_Q$ with $Q \notin N$; and every place $P$ of the domain of $\mathrm{An}(x)$ specialises to $s$, in the sense that for every $f \in R_0.\mathrm{integers}$ regular wherever $j$ is and with $R_0$-residue in the valuation subring of $s$, and every $a \in A$ whose reduction is $s.\mathrm{evalAt}$ of that residue, the difference $P.\mathrm{evalAt}$ of the image of $f$ in `fieldBar q M'` minus $a$ lies in $A$ and in its maximal ideal. Moreover, distinct $x, x' \in N$ have disjoint annulus domains; for every $\tau$ in the subgroup generated by the `levelAutBar q M' ζ γ` with $\gamma \in \Gamma_0(M')$ that preserves $R.\mathrm{integers}$, and every $x \in N$, the translate $\{P \mid \tau^{-1}\cdot P \in \mathrm{An}(x).\mathrm{dom}\}$ is the domain of $\mathrm{An}$ at the translated place; and the charts and annuli cover all specialisations to $s$: every rational place $P$ of `fieldBar q M'` over $\overline{\mathbb{Q}}$ satisfying the specialisation condition just described lies either in $D_Q$ for some $Q \notin N$ or in the domain of $\mathrm{An}(x)$ for some $x \in N$.
--
--   This is the $q = 3$ instance, at the rigidifying auxiliary level provided by a prime $\ell \equiv 11 \pmod{12}$ dividing $M'$, of the construction of the supersingular part of the semistable model of the modular curve of full level $q$ over a valuation ring above $q$: smooth-point charts with their residue discs, annuli around the $q+1$ nodes, transitivity of the level action on the nodes, finitely many generators of the ring of functions regular outside the nodes, and the identification of the supersingular component with a quotient of the Drinfeld curve $xy^q - x^qy = 1$, equivariantly for $\Gamma_0(M')$ and for semilinear Galois automorphisms. It is used by [`ModularCurve.FullLevel.exists_algEquiv_quotField_of_chart_over_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.exists_algEquiv_quotField_of_chart_over_of_eq_three_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_supersingularRegularProlongation_smoothPointCharts_nodeFrames_levelOrbits_generators_of_eq_three_of_dvd.lean

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

theorem ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodeFrames_levelOrbits_generators_of_eq_three_of_dvd
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
            Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
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
