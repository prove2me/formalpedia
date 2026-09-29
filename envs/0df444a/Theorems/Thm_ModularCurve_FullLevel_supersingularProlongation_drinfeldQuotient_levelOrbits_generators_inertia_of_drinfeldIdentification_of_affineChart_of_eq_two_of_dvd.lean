-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_drinfeldQuotient_levelOrbits_generators_inertia_of_drinfeldIdentification_of_affineChart_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.supersingularProlongation_drinfeldQuotient_levelOrbits_generators_inertia_of_drinfeldIdentification_of_affineChart_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/92ed5ca9-7779-5be4-b3f4-1a7557c92cbd
-- title:
--   Level orbits and generators for the q=2 supersingular prolongation
-- statement:
--   Throughout, $q$ is a prime with $q = 2$ (hypothesis `hq2`), $M'$ is a nonzero natural number not divisible by $q$ (`hqM'`), and a rigidifying auxiliary prime $\ell$ is fixed with $\ell$ prime, $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$ (`hℓ`, `hℓ12`, `hℓM'`). Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ is a nonunit of $A$ (`hA`), and $\kappa := \mathrm{ResidueField}\,A$ denotes its residue field. Two function fields occur: $\mathrm{modularFunctionFieldBar}\,M'$, the base change to $\overline{\mathbb{Q}}$ of the full level-$M'$ modular function field inside Laurent series, and $\mathrm{fieldBar}\,q\,M' = \mathrm{xHFunctionFieldBar}\,(q^2M')\,(\mathrm{levelH}\,q\,M')$, the corresponding base change of the $\Gamma_H(q^2M')$ $q$-expansion function field, where $\mathrm{levelH}\,q\,M'$ is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, i.e. the units congruent to $1$ modulo $q$. The hypothesis `hle` asserts the inclusion $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$.
--
--   A finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ over $\kappa$ is given, and `hW` says that $W$ consists exactly of the supersingular places, namely those $w$ which are rational, satisfy `IsAffineGeomPlace`, and whose value $w.\mathrm{evalAt}(\mathrm{jGeomGen}\,\kappa\,M')$ lies in `ssJSet q κ`; an element $s \in W$ is fixed. The reduction of the level-$M'$ field is given by a `ConstantReduction` $R_0$ of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ (a valuation subring $R_0.\mathrm{integers}$, a surjective residue map onto the reduced field with kernel the maximal ideal, a place map, and the compatibilities recorded in that structure), together with the hypothesis `hR₀`: for every Laurent series $y$ over $A$ whose coefficientwise image in Laurent series over $\overline{\mathbb{Q}}$ lies in $\mathrm{modularFunctionFieldBar}\,M'$, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue is, as a Laurent series over $\kappa$, the coefficientwise reduction of $y$. An element $\pi \in \overline{\mathbb{Q}}$ is fixed with $\pi^{q^2-1} = q$ (`hπ`) and $\pi \in A$ (`hπP`).
--
--   On the special-fibre side, $FSS$ is a field over $\kappa$ and $R$ is a `RegularProlongation` of $A$ from $\mathrm{fieldBar}\,q\,M'$ to $FSS$ (a valuation subring $R.\mathrm{integers}$ meeting $\overline{\mathbb{Q}}$ in $A$, with surjective residue map to $FSS$ whose kernel is the maximal ideal and which is compatible with reduction from $A$). A finite set $N$ of places of $FSS$ over $\kappa$ is given, together with families assigning to each place $Q$ of $FSS$ a subring $S_Q \le \mathrm{fieldBar}\,q\,M'$ (`Sx`), a ring homomorphism $\varphi_Q : A[T] \to S_Q$ (`φx`), a ring homomorphism $\chi_{0,Q} : S_Q \to \kappa$ (`χ₀x`), and a set $D_Q$ of places of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb{Q}}$ (`Dx`).
--
--   The hypotheses on these data are: `h0`, that $FSS$ contains an element transcendental over $\kappa$; `h1`, that $R$ lies over $s$, i.e. for $f \in R_0.\mathrm{integers}$ which has nonnegative order at every place of $\mathrm{modularFunctionFieldBar}\,M'$ at which the coefficientwise image of the $q$-expansion $jq$ has nonnegative order, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $R.\mathrm{integers}$ and its $R$-residue is the image in $FSS$ of $s.\mathrm{evalAt}$ applied to that $R_0$-residue; `h2`, that for every $\zeta \in \mathrm{Idx}\,q$ (a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$) and every $\gamma \in \Gamma_0(M') \le SL(2,\mathbb{Z})$ the pullback of $R.\mathrm{integers}$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ equals $R.\mathrm{integers}$; `hcard`, that $|N| = q+1$; and `hpkg`, which attaches to each place $Q \notin N$ a smooth-point package of fourteen clauses (summarised here): the image of $A$ lies in $S_Q$; $\varphi_Q$ is formally smooth and formally unramified; $\varphi_Q$ sends constants $C\,a$ to the images of $a$, and $\chi_{0,Q}\varphi_Q(C\,a)$ is the residue of $a$ while $\chi_{0,Q}\varphi_Q(X) = 0$; each $c$ in the maximal ideal of $A$ admits a unique $A$-point $\chi : S_Q \to A$ which is the identity on constants, reduces to $\chi_{0,Q}$ and sends $\varphi_Q(X)$ to $c$; every $f \in S_Q$ lies in $R.\mathrm{integers}$, its $R$-residue lies in the valuation subring of $Q$ and reduces there to the image of $\chi_{0,Q}(f)$; the $R$-residue of $\varphi_Q(X)$ has $Q$-order $1$; $D_Q$ consists exactly of the rational places $P$ at which all of $S_Q$ is regular with values in $A$ and for which $A$-valuation of $P.\mathrm{evalAt}(f)$ is $<1$ precisely when $\chi_{0,Q}(f) = 0$; each $A$-point of $S_Q$ lifting $\chi_{0,Q}$ is realised by a unique $P \in D_Q$; for $P \in D_Q$ the valuation subring of $P$ consists of the fractions $g/h$ with $g,h \in S_Q$ and $P.\mathrm{evalAt}(h) \ne 0$; a nonzero $f$ of order $0$ at all $P \in D_Q$ becomes, after multiplication by a nonzero constant of $\overline{\mathbb{Q}}$, a unit of $S_Q$; and an element of $R.\mathrm{integers}$ regular at all $P \in D_Q$ lies in $S_Q$.
--
--   The remaining hypotheses on the package are: `hdisj`, that the discs $D_Q$ for $Q, Q' \notin N$ are pairwise disjoint (a common member forces $Q = Q'$); `hcusp`, that for $Q \notin N$ and $P \in D_Q$ the order at $P$ of the image in $\mathrm{fieldBar}\,q\,M'$ of the coefficientwise embedding of $jq$ is nonnegative; `heqv`, that for every $\tau$ in the subgroup generated by the automorphisms $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ with $\zeta \in \mathrm{Idx}\,q$ and $\gamma \in \Gamma_0(M')$, and every witness that $\tau$ preserves $R.\mathrm{integers}$, the induced residue automorphism $R.\mathrm{resAut}\,\tau$ preserves $N$ and satisfies $\mathrm{smulDisc}\,\tau\,(D_Q) = D_{R.\mathrm{resAut}\,\tau\,\cdot\,Q}$ for $Q \notin N$; and `hUniq`, that the package is unique: for $Q \notin N$ any quadruple $(S,\varphi,\chi_0,D)$ satisfying the same fourteen clauses has $D = D_Q$, $S = S_Q$, and $\chi_0$ agreeing with $\chi_{0,Q}$ on common elements.
--
--   Two Drinfeld-side identifications are assumed as data. `hE1` asserts: for every algebra structure of $\mathbb{F}_{q^2} = \mathrm{GaloisField}\,q\,2$ on $\kappa$, assuming $\mathrm{DrinfeldCurve.CoordRing}\,q\,\kappa$ is a domain, and for every $\zeta \in \mathrm{Idx}\,q$, there are a subgroup $C_s$ of the $(q+1)$-st roots of unity of $\mathbb{F}_{q^2}$ and a $\kappa$-algebra isomorphism $e$ from $FSS$ onto $\mathrm{DrinfeldCurve.quotField}\,q\,\kappa\,C_s$ (the fixed field of the subgroup of $\mathrm{hFunctionFieldAction}$ generated by the elements $(1,\zeta')$, $\zeta' \in C_s$, inside the Drinfeld function field) such that $\mathrm{Nat.card}\,C_s = \mathrm{placeWidthChar}\,q\,M'\,s$ — at $q = 2$ this is $12$ or $1$, according as $s.\mathrm{evalAt}(\mathrm{jGeomGen})$ vanishes or not, divided by $\mathrm{placeRamificationJ}\,M'\,s$ — and such that for every $\gamma \in \Gamma_0(M')$, given that $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma^{-1}$ preserves $R.\mathrm{integers}$ and that $(\mathrm{redQ}\,q\,\gamma, 1)$ lies in $\mathrm{hSubgroup}\,q$, the map $e$ intertwines the residue automorphism $R.\mathrm{resAut}(\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma^{-1})$ with $\mathrm{hFunctionFieldAction}$ of $(\mathrm{redQ}\,q\,\gamma,1)$. `hDLplus` asserts the same identification enriched by the inertia law: for every ring homomorphism $\iota : \mathbb{F}_{q^2} \to \kappa$, used as the algebra structure, and assuming the coordinate ring is a domain, there is a subgroup $C_s$ with $\mathrm{Nat.card}\,C_s = \mathrm{placeWidthChar}\,q\,M'\,s$ such that for every $\zeta$ there are an exponent $\eta \in \{1,q\}$ and an isomorphism $e$ as above which, besides the $\Gamma_0(M')$-intertwining just described, satisfies: for every $\tau$ in $A.\mathrm{inertiaSubgroupIn}\,\mathbb{Q}$, every $\alpha \in \mathbb{F}_{q^2}^\times$ with $\iota(\alpha) = A.\mathrm{tameCharacter}\,\pi\,\tau$ (the residue of $\tau\pi/\pi$), and every semilinear automorphism $g$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb{Q}}$ equal to $\mathrm{arithmeticGalois}(\mathrm{xHFunctionField}\,(q^2M')\,(\mathrm{levelH}\,q\,M'))\,\tau$, the automorphism $g$ preserves $R.\mathrm{integers}$, and for every ring automorphism $\varphi$ of $FSS$ inducing the action of $g$ on $R$-residues, every $d \in (\mathbb{Z}/q)^\times$ whose image in $\mathbb{F}_{q^2}$ equals $\alpha^{q+1}$, and every witness that $(\mathrm{diagOneElem}\,q\,(d^\eta)^{-1}, \alpha^\eta)$ lies in $\mathrm{hSubgroup}\,q$, the map $e$ intertwines $\varphi$ with $\mathrm{hFunctionFieldAction}$ of that element. Finally, `haff` provides an affine chart off the ends: a subring $B \le \mathrm{fieldBar}\,q\,M'$ containing the image of $A$, contained in $R.\mathrm{integers}$ and in $S_Q$ for every $Q \notin N$, and such that every $z \in FSS$ lying in the valuation subring of every $Q \notin N$ is the $R$-residue of some element of $B$.
--
--   Under these hypotheses the conclusion is the conjunction of five statements. First, the statement `hE1` above, verbatim. Second, transitivity of the level action on $N$: for all places $x, x' \in N$ there exist $\zeta \in \mathrm{Idx}\,q$, $\gamma \in \Gamma_0(M')$ and a witness that $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ preserves $R.\mathrm{integers}$, with $R.\mathrm{resAut}(\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma) \cdot x = x'$. Third, every place off $N$ is moved: for each $Q \notin N$ there exist $\zeta$, $\gamma \in \Gamma_0(M')$ and such a witness with $R.\mathrm{resAut}(\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma) \cdot Q \ne Q$. Fourth, a finite generating set: there exist $n \in \mathbb{N}$ and $g : \mathrm{Fin}\,n \to \mathrm{fieldBar}\,q\,M'$ with all $g_i \in R.\mathrm{integers}$, such that each $g_i$ lies in the valuation subring of every $P \in D_Q$ for every $Q \notin N$ with $P.\mathrm{evalAt}(g_i) \in A$, and such that every $f \in FSS$ lying in the valuation subring of every $Q \notin N$ belongs to the $\kappa$-subalgebra of $FSS$ generated by the residues $R.\mathrm{residue}(g_i)$. Fifth, the statement `hDLplus` above, verbatim.
--
--   This is the $q = 2$ case, under the rigid auxiliary level guard given by $\ell \equiv 11 \pmod{12}$ dividing $M'$, of the Drinfeld-quotient description of the component of the semistable special fibre above a supersingular point of $X_0(M')$: it carries the identification of the reduced field with a quotient of the Drinfeld function field (with both the $\Gamma_0(M')$ law and the tame inertia law) through, and adds that the level automorphisms act transitively on the $q+1$ ends, move every place off the ends, and that the functions regular off the ends are generated by finitely many reductions. It feeds the assembly theorem [`ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.exists_supersingularRegularProlongation_smoothPointCharts_nodePresentations_crossUnits_igusaOverS_inertia_nodeCharts_hasseJ_of_eq_two_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_drinfeldQuotient_levelOrbits_generators_inertia_of_drinfeldIdentification_of_affineChart_of_eq_two_of_dvd.lean

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
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.supersingularProlongation_drinfeldQuotient_levelOrbits_generators_inertia_of_drinfeldIdentification_of_affineChart_of_eq_two_of_dvd
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
    (s : ↥W)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (FSS : Type) [Field FSS] [Algebra (ResidueField A) FSS]
    (R : RegularProlongation A (fieldBar q M') FSS)
    (N : Finset (Place (ResidueField ↥A) FSS))
    (Sx : Place (ResidueField ↥A) FSS → Subring ↥(fieldBar q M'))
    (φx : (Q : Place (ResidueField ↥A) FSS) → (Polynomial ↥A →+* ↥(Sx Q)))
    (χ₀x : (Q : Place (ResidueField ↥A) FSS) → (↥(Sx Q) →+* ResidueField ↥A))
    (Dx : Place (ResidueField ↥A) FSS → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M')))
    (h0 : (∃ t : FSS, Transcendental (ResidueField A) t))
    (h1 : (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers,
            R.residue ⟨_, hC⟩ = algebraMap (ResidueField A) FSS
              ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
                (R₀.residue ⟨f, hf⟩))))
    (h2 : (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
        R.integers.comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom = R.integers))
    (hcard : N.card = q + 1)
    (hpkg : (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →

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
          (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ Dx Q, f ∈ P.toValuationSubring) → f ∈ Sx Q)))
    (hdisj : (∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N → Q' ∉ N → ∀ P, P ∈ Dx Q → P ∈ Dx Q' → Q = Q'))
    (hcusp : (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P ∈ Dx Q, 0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : fieldBar q M')))
    (heqv : (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
            ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
          ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
            (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N) ∧
            (Q ∉ N → AlgebraicCurve.RegularProlongation.smulDisc τ (Dx Q) = Dx (R.resAut τ hτ • Q))))

    (hUniq : (∀ Q ∉ N, ∀ (S : Subring ↥(fieldBar q M')) (φ : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A)
          (D : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
          (
            (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ S) ∧
            (φ).FormallySmooth ∧ (φ).FormallyUnramified ∧
            (∀ a : ↥A, ((φ (Polynomial.C a) : ↥(S)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ))) ∧
            (∀ a : ↥A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
            χ₀ (φ Polynomial.X) = 0 ∧
            (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
              ∃! χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) ∧
                (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φ Polynomial.X) = c) ∧
            (∀ f : ↥(S), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
              IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f)) ∧
            (∃ hR : ((φ Polynomial.X : ↥(S)) : ↥(fieldBar q M')) ∈ R.integers,
              Q.ord (R.residue ⟨((φ Polynomial.X : ↥(S)) : ↥(fieldBar q M')), hR⟩) = 1) ∧
            (∀ P, P ∈ D ↔ (P.IsRational ∧ (∀ f : ↥(S), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
              (∀ f : ↥(S), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χ₀ f = 0))) ∧
            (∀ χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) →
              (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) →
              ∃! P, P ∈ D ∧ ∀ f : ↥(S), P.evalAt (f : ↥(fieldBar q M')) = ((χ f : ↥A) : (AlgebraicClosure ℚ))) ∧
            (∀ P ∈ D, ∀ f : ↥(fieldBar q M'), f ∈ P.toValuationSubring ↔
              ∃ g h : ↥(S), P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
              ∃ (c : (AlgebraicClosure ℚ)) (u : (↥(S))ˣ), c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * f = ((u : ↥(S)) : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S)) →
          (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ D ↔ P ∈ Dx Q) ∧
          (∀ f : ↥(fieldBar q M'), f ∈ S ↔ f ∈ Sx Q) ∧
          (∀ (f : ↥(fieldBar q M')) (hf : f ∈ S) (hf' : f ∈ Sx Q), χ₀ ⟨f, hf⟩ = χ₀x Q ⟨f, hf'⟩)))

    (hE1 : (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
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
                    DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))))
    (hDLplus : (∀ (ι : GaloisField q 2 →+* ResidueField ↥A),
          letI : Algebra (GaloisField q 2) (ResidueField ↥A) := ι.toAlgebra
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2))),
            Nat.card Cs = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            ∀ (ζ : Idx q), ∃ η : ℕ, (η = 1 ∨ η = q) ∧ ∃ (e : FSS ≃ₐ[ResidueField ↥A] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
              (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
                ∀ (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ⁻¹ f ∈ R.integers ↔ f ∈ R.integers)
                  (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
                  ∀ x : FSS,
                    ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                      DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) ∧
              (∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
                ι (α : GaloisField q 2) = A.tameCharacter π τ →
                ∀ (g : SemilinearAut (AlgebraicClosure ℚ) ↥(fieldBar q M')),
                  g = ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ →
                (∀ f : ↥(fieldBar q M'), g • f ∈ R.integers ↔ f ∈ R.integers) ∧
                ∀ (hst : ∀ f : ↥(fieldBar q M'), g • f ∈ R.integers ↔ f ∈ R.integers)
                  (φ : FSS ≃+* FSS),
                  (∀ (f : ↥(fieldBar q M')) (hf : f ∈ R.integers),
                    R.residue ⟨g • f, (hst f).mpr hf⟩ = φ (R.residue ⟨f, hf⟩)) →
                  ∀ (d : (ZMod q)ˣ), algebraMap (ZMod q) (GaloisField q 2) (d : ZMod q) = (α : GaloisField q 2) ^ (q + 1) →
                    ∀ (hmem : (diagOneElem q (d ^ η)⁻¹, α ^ η) ∈ DrinfeldCurve.hSubgroup q),
                      ∀ x : FSS,
                        ((e (φ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                          DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))))

    (haff : ∃ B : Subring ↥(fieldBar q M'),

        (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ B) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ R.integers) ∧

        (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ Sx Q) ∧

        (∀ z : FSS, (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → z ∈ Q.toValuationSubring) →
          ∃ (f : ↥(fieldBar q M')) (_ : f ∈ B) (hfR : f ∈ R.integers), R.residue ⟨f, hfR⟩ = z)) :
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
        (∀ (ι : GaloisField q 2 →+* ResidueField ↥A),
          letI : Algebra (GaloisField q 2) (ResidueField ↥A) := ι.toAlgebra
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2))),
            Nat.card Cs = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            ∀ (ζ : Idx q), ∃ η : ℕ, (η = 1 ∨ η = q) ∧ ∃ (e : FSS ≃ₐ[ResidueField ↥A] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
              (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
                ∀ (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ⁻¹ f ∈ R.integers ↔ f ∈ R.integers)
                  (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
                  ∀ x : FSS,
                    ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                      DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) ∧
              (∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
                ι (α : GaloisField q 2) = A.tameCharacter π τ →
                ∀ (g : SemilinearAut (AlgebraicClosure ℚ) ↥(fieldBar q M')),
                  g = ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ →
                (∀ f : ↥(fieldBar q M'), g • f ∈ R.integers ↔ f ∈ R.integers) ∧
                ∀ (hst : ∀ f : ↥(fieldBar q M'), g • f ∈ R.integers ↔ f ∈ R.integers)
                  (φ : FSS ≃+* FSS),
                  (∀ (f : ↥(fieldBar q M')) (hf : f ∈ R.integers),
                    R.residue ⟨g • f, (hst f).mpr hf⟩ = φ (R.residue ⟨f, hf⟩)) →
                  ∀ (d : (ZMod q)ˣ), algebraMap (ZMod q) (GaloisField q 2) (d : ZMod q) = (α : GaloisField q 2) ^ (q + 1) →
                    ∀ (hmem : (diagOneElem q (d ^ η)⁻¹, α ^ η) ∈ DrinfeldCurve.hSubgroup q),
                      ∀ x : FSS,
                        ((e (φ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                          DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) := by sorry
