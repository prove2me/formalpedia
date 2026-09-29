-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_drinfeldQuotient_levelOrbits_generators_inertia_of_drinfeldIdentification_of_affineChart_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.supersingularProlongation_drinfeldQuotient_levelOrbits_generators_inertia_of_drinfeldIdentification_of_affineChart_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/73b82b24-a863-508c-af68-4338d070ad48
-- title:
--   Level orbits and affine generators for the supersingular prolongation at q=3
-- statement:
--   Setting. A prime $q$ subject to $q=3$; a natural number $M'\neq 0$ with $q\nmid M'$; a prime $\ell$ with $\ell\equiv 11\pmod{12}$ and $\ell\mid M'$ (a rigidity guard at the auxiliary level); a valuation subring $A\subseteq\overline{\mathbb{Q}}$ with $A.\mathrm{LiesOverPrime}\ q$, i.e. $q$ is a non-unit of $A$, with residue field $\kappa=\mathrm{ResidueField}\ A$; a finite set $W$ of places of the intermediate field $\mathrm{modularFunctionFieldC}\ \kappa\ M'\subseteq\kappa((t))$ whose members are, by `hW`, exactly the supersingular places, that is the places $w$ that are rational (the structure map $\kappa\to w.\mathrm{ResidueField}$ is onto), are affine geometric places, and satisfy $w.\mathrm{evalAt}(\mathrm{jGeomGen})\in \mathrm{ssJSet}\ q\ \kappa$; an inclusion `hle` of $\mathrm{modularFunctionFieldBar}\ M'$ (the $\overline{\mathbb{Q}}$-base change, inside $\overline{\mathbb{Q}}((t))$, of the full level-$M'$ modular function field) into $\mathrm{fieldBar}\ q\ M'=\mathrm{xHFunctionFieldBar}(q^2M')(\mathrm{levelH}\ q\ M')$, where $\mathrm{levelH}\ q\ M'$ is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times$; a constant reduction $R_0$ of $A$ from $\mathrm{modularFunctionFieldBar}\ M'$ to $\mathrm{modularFunctionFieldC}\ \kappa\ M'$, required by `hR₀` to be compatible with coefficientwise reduction: every Laurent series $y$ over $A$ whose image under $A\hookrightarrow\overline{\mathbb{Q}}$ lies in $\mathrm{modularFunctionFieldBar}\ M'$ lies in $R_0.\mathrm{integers}$ and its $R_0$-residue is the coefficientwise residue of $y$; a chosen $s\in W$; and an element $\pi\in A$ with $\pi^{q^2-1}=q$.
--
--   The prolongation data. A field $F_{ss}$ that is a $\kappa$-algebra; a regular prolongation $R$ of $A$ from $\mathrm{fieldBar}\ q\ M'$ to $F_{ss}$ (a valuation subring $R.\mathrm{integers}$ of $\mathrm{fieldBar}\ q\ M'$ meeting $\overline{\mathbb{Q}}$ in $A$, together with a surjective residue map onto $F_{ss}$ with kernel the maximal ideal, compatible with $A\to\kappa$, and with the scaling property that every nonzero element becomes a unit-residue integral element after multiplication by a constant); a finite set $N$ of places of $F_{ss}$ over $\kappa$; and families, indexed by the places $Q$ of $F_{ss}$ over $\kappa$, consisting of subrings $S_x(Q)\subseteq \mathrm{fieldBar}\ q\ M'$, ring maps $\varphi_x(Q):A[T]\to S_x(Q)$, ring maps $\chi_{0x}(Q):S_x(Q)\to\kappa$, and sets $D_x(Q)$ of places of $\mathrm{fieldBar}\ q\ M'$ over $\overline{\mathbb{Q}}$.
--
--   Hypotheses on these data. `h0`: $F_{ss}$ contains an element transcendental over $\kappa$. `h1` ($R$ lies over $s$): for every $f\in R_0.\mathrm{integers}$ which is regular wherever the image of the $q$-expansion $\mathrm{jq}$ of $j$ is regular (at every place $P$ of $\mathrm{modularFunctionFieldBar}\ M'$, non-negativity of $P.\mathrm{ord}$ of that image implies $0\le P.\mathrm{ord}(f)$) and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $\mathrm{fieldBar}\ q\ M'$ lies in $R.\mathrm{integers}$ and its $R$-residue is the image in $F_{ss}$ of $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$. `h2` (level-invariance): for every $\zeta\in \mathrm{Idx}\ q$ (a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$) and every $\gamma\in\Gamma_0(M')$, the pullback of $R.\mathrm{integers}$ along $\mathrm{levelAutBar}\ q\ M'\ \zeta\ \gamma$ is $R.\mathrm{integers}$. `hcard`: $N$ has exactly $q+1$ elements. `hpkg` (a smooth-point package at each place off $N$; thirteen clauses, summarised here): for every $Q\notin N$ the image of $A$ lies in $S_x(Q)$; $\varphi_x(Q)$ is formally smooth and formally unramified; $\varphi_x(Q)$ is the structure map on constants and $\chi_{0x}(Q)\circ\varphi_x(Q)$ is the residue map $A\to\kappa$ on constants while killing $T$; each $c$ in the maximal ideal of $A$ is the value at $T$ of a unique section $S_x(Q)\to A$ of $\varphi_x(Q)$ on constants lifting $\chi_{0x}(Q)$; every $f\in S_x(Q)$ is $R$-integral with $R$-residue in the valuation subring of $Q$, whose residue there is the image of $\chi_{0x}(Q)f$; the $R$-residue of $\varphi_x(Q)T$ has order $1$ at $Q$; $D_x(Q)$ consists exactly of the rational places $P$ at which all of $S_x(Q)$ is regular with values in $A$ and at which the values of $f$ have valuation $<1$ precisely when $\chi_{0x}(Q)f=0$; each section as above is realised by a unique $P\in D_x(Q)$; for $P\in D_x(Q)$ the valuation subring of $P$ consists of the fractions $g/h$ with $g,h\in S_x(Q)$ and $P.\mathrm{evalAt}\ h\neq 0$; a nonzero element of order $0$ at all $P\in D_x(Q)$ becomes a unit of $S_x(Q)$ after multiplication by a nonzero constant; and an $R$-integral element regular at all $P\in D_x(Q)$ lies in $S_x(Q)$. `hdisj`: discs attached to distinct places off $N$ are disjoint. `hcusp`: for $Q\notin N$ every $P\in D_x(Q)$ has non-negative order on the image in $\mathrm{fieldBar}\ q\ M'$ of the $q$-expansion of $j$. `heqv` (equivariance): for every $\tau$ in the subgroup generated by the automorphisms $\mathrm{levelAutBar}\ q\ M'\ \zeta\ \gamma$ with $\gamma\in\Gamma_0(M')$ that preserves $R.\mathrm{integers}$, the induced automorphism $R.\mathrm{resAut}\ \tau$ of $F_{ss}$ preserves $N$ setwise, and for $Q\notin N$ one has $\mathrm{smulDisc}\ \tau\ (D_x(Q))=D_x(R.\mathrm{resAut}\ \tau\cdot Q)$. `hUniq` (rigidity of the packages): for $Q\notin N$, any quadruple $(S,\varphi,\chi_0,D)$ satisfying the same thirteen clauses has $D=D_x(Q)$, $S=S_x(Q)$, and $\chi_0$ equal to $\chi_{0x}(Q)$ on common elements.
--
--   The two Drinfeld hypotheses. `hE1`: for every $\mathbb{F}_{q^2}$-algebra structure on $\kappa$ (via `GaloisField q 2`), assuming $\mathrm{CoordRing}\ q\ \kappa$ is a domain, and for every $\zeta\in\mathrm{Idx}\ q$, there exist a subgroup $C$ of the $(q+1)$-st roots of unity of $\mathbb{F}_{q^2}$ and a $\kappa$-algebra isomorphism $e:F_{ss}\to\mathrm{quotField}\ q\ \kappa\ C$ (the fixed field, in the Drinfeld function field, of the subgroup generated by the $H$-action of the elements $(1,\zeta)$ for $\zeta\in C$) such that $\#C=2\cdot\mathrm{placeWidthChar}\ q\ M'\ s$, and such that for every $\gamma\in\Gamma_0(M')$ for which $\mathrm{levelAutBar}\ q\ M'\ \zeta\ \gamma^{-1}$ preserves $R.\mathrm{integers}$, and with $(\mathrm{redQ}\ q\ \gamma,1)$ in $\mathrm{hSubgroup}\ q$, the map $e$ intertwines $R.\mathrm{resAut}(\mathrm{levelAutBar}\ q\ M'\ \zeta\ \gamma^{-1})$ with $\mathrm{hFunctionFieldAction}$ at $(\mathrm{redQ}\ q\ \gamma,1)$. `hDLplus`: for every ring map $\iota:\mathbb{F}_{q^2}\to\kappa$, used as the algebra structure, and assuming $\mathrm{CoordRing}\ q\ \kappa$ is a domain, there is a single subgroup $C$ with $\#C=2\cdot\mathrm{placeWidthChar}\ q\ M'\ s$ such that for every $\zeta$ there are $\eta\in\{1,q\}$ and an isomorphism $e:F_{ss}\to\mathrm{quotField}\ q\ \kappa\ C$ satisfying the same $\Gamma_0(M')$-law and, in addition, the tame inertia law: for $\tau$ in $A.\mathrm{inertiaSubgroupIn}\ \mathbb{Q}$, for $\alpha\in\mathbb{F}_{q^2}^\times$ with $\iota(\alpha)=A.\mathrm{tameCharacter}\ \pi\ \tau$, and for the semilinear automorphism $g$ of $\mathrm{fieldBar}\ q\ M'$ given by $\mathrm{arithmeticGalois}$ of $\tau$ on $\mathrm{xHFunctionField}(q^2M')(\mathrm{levelH}\ q\ M')$, the set $R.\mathrm{integers}$ is $g$-stable, and every ring automorphism $\phi$ of $F_{ss}$ induced by $g$ on residues satisfies, for every $d\in(\mathbb{Z}/q)^\times$ whose image in $\mathbb{F}_{q^2}$ is $\alpha^{q+1}$ and with $(\mathrm{diagOneElem}\ q\ (d^{\eta})^{-1},\alpha^{\eta})\in\mathrm{hSubgroup}\ q$, that $e$ intertwines $\phi$ with $\mathrm{hFunctionFieldAction}$ at that element.
--
--   The affine chart hypothesis `haff`: there is a subring $B\subseteq\mathrm{fieldBar}\ q\ M'$ containing the image of $A$, contained in $R.\mathrm{integers}$, contained in $S_x(Q)$ for every $Q\notin N$, and such that every $z\in F_{ss}$ lying in the valuation subring of every $Q\notin N$ is the $R$-residue of some element of $B$.
--
--   Conclusion. The conjunction of five assertions.
--
--   (1) The statement of `hE1` verbatim: for every $\mathbb{F}_{q^2}$-algebra structure on $\kappa$, with $\mathrm{CoordRing}\ q\ \kappa$ a domain, and every $\zeta\in\mathrm{Idx}\ q$, there are $C$ and a $\kappa$-algebra isomorphism $e:F_{ss}\to\mathrm{quotField}\ q\ \kappa\ C$ with $\#C=2\cdot\mathrm{placeWidthChar}\ q\ M'\ s$ and with the $\Gamma_0(M')$-equivariance described above.
--
--   (2) The level automorphisms act transitively on $N$: for all $x,x'\in N$ there are $\zeta\in\mathrm{Idx}\ q$ and $\gamma\in\Gamma_0(M')$ such that $\mathrm{levelAutBar}\ q\ M'\ \zeta\ \gamma$ preserves $R.\mathrm{integers}$ and $R.\mathrm{resAut}(\mathrm{levelAutBar}\ q\ M'\ \zeta\ \gamma)\cdot x=x'$.
--
--   (3) No place off $N$ is fixed by all of them: for every place $Q\notin N$ of $F_{ss}$ over $\kappa$ there are $\zeta$ and $\gamma\in\Gamma_0(M')$ with $\mathrm{levelAutBar}\ q\ M'\ \zeta\ \gamma$ preserving $R.\mathrm{integers}$ and $R.\mathrm{resAut}(\mathrm{levelAutBar}\ q\ M'\ \zeta\ \gamma)\cdot Q\neq Q$.
--
--   (4) Finitely many generators for the affine part: there are $n\in\mathbb{N}$ and $g:\mathrm{Fin}\ n\to\mathrm{fieldBar}\ q\ M'$ with each $g(i)\in R.\mathrm{integers}$, such that for every $i$, every $Q\notin N$ and every $P\in D_x(Q)$ the element $g(i)$ lies in the valuation subring of $P$ with $P.\mathrm{evalAt}(g(i))\in A$, and such that every $f\in F_{ss}$ lying in the valuation subring of every $Q\notin N$ belongs to the $\kappa$-subalgebra of $F_{ss}$ generated by the residues $R.\mathrm{residue}(g(i))$, $i<n$.
--
--   (5) The statement of `hDLplus` verbatim, with the uniform subgroup $C$, the exponents $\eta\in\{1,q\}$, the $\Gamma_0(M')$-law and the tame inertia law exactly as listed above.
--
--   Thus conjuncts (1) and (5) repeat the hypotheses `hE1` and `hDLplus` unchanged, and the added content is (2), (3) and (4).
--
--   This is the $q=3$ case, at a rigid auxiliary level carrying a prime $\ell\equiv 11\pmod{12}$ dividing $M'$, of the step which, from a Drinfeld-style identification of the reduced field $F_{ss}$ at a supersingular point with a quotient of the Drinfeld function field, extracts the geometric information needed for the semistable model: that the level automorphisms permute the $q+1$ ends transitively, fix no other place of the supersingular component, and that the affine part of the component is generated by finitely many residues of functions regular on the smooth-point discs. It is used in the assembly of supersingular regular prolongations together with their smooth-point charts, node presentations, crossing units and inertia data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_drinfeldQuotient_levelOrbits_generators_inertia_of_drinfeldIdentification_of_affineChart_of_eq_three_of_dvd.lean

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

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.supersingularProlongation_drinfeldQuotient_levelOrbits_generators_inertia_of_drinfeldIdentification_of_affineChart_of_eq_three_of_dvd
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
            Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
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
            Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
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
            Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
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
            Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
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
