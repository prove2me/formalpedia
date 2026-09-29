-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_exists_generators_regular_off_ends_of_affineChart_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.supersingularProlongation_exists_generators_regular_off_ends_of_affineChart_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/3e71981b-bf5b-5012-b236-cd7cf3bbeaa9
-- title:
--   R-integral generators regular off the ends, q=3
-- statement:
--   Fix a prime $q$ with $q = 3$ and a natural number $M' \neq 0$ with $q \nmid M'$, together with a prime $\ell$ satisfying $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ is a non-unit of $A$, and write $\kappa = \mathrm{ResidueField}\,A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ over $\kappa$ whose members are, by `hW`, exactly the supersingular places, i.e. the places $w$ that are rational, are affine geometric places, and satisfy $w.\mathrm{evalAt}(\mathrm{jGeomGen}\,\kappa\,M') \in \mathrm{ssJSet}\,q\,\kappa$; let $s \in W$ be one of them. Let `hle` be the inclusion $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ of intermediate fields of $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ over $\overline{\mathbb{Q}}$, the larger field being the base change to $\overline{\mathbb{Q}}$ of the function field of level $\Gamma_H(q^2M')$ for $H = \mathrm{levelH}\,q\,M'$. Let $R_0$ be a constant reduction of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}\,\kappa\,M'$: a valuation subring $R_0.\mathrm{integers}$ meeting $\overline{\mathbb{Q}}$ exactly in $A$, a surjective residue homomorphism onto $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ with kernel the maximal ideal and compatible with reduction on $A$, a scaling clause making every nonzero function have nonzero reduction after multiplication by a constant, and a map on places preserving degrees and compatible with divisors. The hypothesis `hR₀` requires that for every Laurent series $y$ with coefficients in $A$ whose image in $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ lies in $\mathrm{modularFunctionFieldBar}\,M'$, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue is the coefficientwise reduction of $y$ along $A \to \kappa$.
--
--   The remaining data describe the supersingular component. Let $F_{ss}$ be a field which is a $\kappa$-algebra, $R$ a regular prolongation of $A$ from $\mathrm{fieldBar}\,q\,M'$ to $F_{ss}$ (a valuation subring $R.\mathrm{integers}$ meeting $\overline{\mathbb{Q}}$ exactly in $A$, with surjective residue map onto $F_{ss}$ whose kernel is the maximal ideal, compatible with reduction on $A$, and satisfying the same scaling clause), $N$ a finite set of places of $F_{ss}$ over $\kappa$, and, indexed by places $Q$ of $F_{ss}$ over $\kappa$, a subring $S_x(Q) \subseteq \mathrm{fieldBar}\,q\,M'$, a ring homomorphism $\varphi_x(Q) : A[T] \to S_x(Q)$, a ring homomorphism $\chi_{0x}(Q) : S_x(Q) \to \kappa$, and a set $D_x(Q)$ of places of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb{Q}}$.
--
--   These are subject to the following groups of hypotheses. `h0`: $F_{ss}$ contains an element transcendental over $\kappa$. `h1`: $R$ lies over $s$, namely for every $f \in R_0.\mathrm{integers}$ which has non-negative order at every place of $\mathrm{modularFunctionFieldBar}\,M'$ at which the image of the $q$-expansion $\mathrm{jq}$ has non-negative order, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $R.\mathrm{integers}$ and its $R$-residue is the image under $\kappa \to F_{ss}$ of $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$. `h2`: for every $\zeta : \mathrm{Idx}\,q$ and every $\gamma \in \Gamma_0(M')$ in $\mathrm{SL}_2(\mathbb{Z})$, the subring $R.\mathrm{integers}$ is stable under the level automorphism $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$, in the sense that its preimage under that automorphism is itself. `hcard`: $N$ has exactly $q+1$ elements. `hpkg` (fourteen clauses, summarised here): for every place $Q \notin N$ the quadruple $(S_x(Q), \varphi_x(Q), \chi_{0x}(Q), D_x(Q))$ is a smooth-point package — $S_x(Q)$ contains the image of $A$; $\varphi_x(Q)$ is formally smooth and formally unramified and sends constants $C\,a$ to the images of $a$; $\chi_{0x}(Q)$ sends $\varphi_x(Q)(C\,a)$ to the residue of $a$ and $\varphi_x(Q)(X)$ to $0$; for each $c \in A$ with zero residue there is a unique $A$-valued section of $S_x(Q)$ splitting the constants, reducing to $\chi_{0x}(Q)$, and sending $\varphi_x(Q)(X)$ to $c$; every element of $S_x(Q)$ is $R$-integral with $R$-residue in the valuation subring of $Q$ and with residue there equal to the image of its $\chi_{0x}(Q)$-value; the $R$-residue of $\varphi_x(Q)(X)$ has order $1$ at $Q$; $D_x(Q)$ consists exactly of the rational places $P$ at which all elements of $S_x(Q)$ are regular with values in $A$, those values having valuation $<1$ precisely on the kernel of $\chi_{0x}(Q)$; the $A$-valued sections splitting the constants and reducing to $\chi_{0x}(Q)$ correspond bijectively to points of $D_x(Q)$ via evaluation; at each $P \in D_x(Q)$ the valuation subring of $P$ is the localisation of $S_x(Q)$ at the functions not vanishing at $P$; a unit principle holds for nonzero functions of order $0$ on all of $D_x(Q)$ (they become units of $S_x(Q)$ after multiplication by a nonzero constant); and every $R$-integral function regular at all $P \in D_x(Q)$ lies in $S_x(Q)$. `hdisj`: the discs attached to distinct places off $N$ are disjoint. `hcusp`: for $Q \notin N$ and $P \in D_x(Q)$, the image of $\mathrm{jq}$ in $\mathrm{fieldBar}\,q\,M'$ has non-negative order at $P$. `heqv`: every $\tau$ in the subgroup generated by the automorphisms $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ with $\gamma \in \Gamma_0(M')$ which stabilises $R.\mathrm{integers}$ induces, through $R.\mathrm{resAut}$, a permutation of places of $F_{ss}$ preserving $N$ and carrying $D_x(Q)$ to $D_x$ of the image of $Q$, for $Q \notin N$, where the transport of discs is $\mathrm{smulDisc}$. `hUniq`: packages off $N$ are unique, i.e. for $Q \notin N$ any quadruple $(S,\varphi,\chi_0,D)$ satisfying the same fourteen clauses satisfies $D = D_x(Q)$, $S = S_x(Q)$ and $\chi_0 = \chi_{0x}(Q)$ on common elements. `hdl`: the Drinfeld identification, namely for every algebra structure of $\mathrm{GaloisField}\,q\,2$ on $\kappa$, assuming $\mathrm{CoordRing}\,q\,\kappa$ is a domain, and for every $\zeta : \mathrm{Idx}\,q$, there exist a subgroup $C_s$ of the $(q+1)$-st roots of unity of $\mathrm{GaloisField}\,q\,2$ and a $\kappa$-algebra isomorphism $e$ from $F_{ss}$ onto $\mathrm{DrinfeldCurve.quotField}\,q\,\kappa\,C_s$ such that $\mathrm{Nat.card}\,C_s = 2\,\mathrm{placeWidthChar}\,q\,M'\,s$ and such that, for $\gamma \in \Gamma_0(M')$ with $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma^{-1}$ stabilising $R.\mathrm{integers}$ and with $(\mathrm{redQ}\,q\,\gamma, 1)$ in $\mathrm{hSubgroup}\,q$, the map $e$ intertwines the induced automorphism $R.\mathrm{resAut}$ of $F_{ss}$ with the action $\mathrm{hFunctionFieldAction}$ of that element on the Drinfeld function field. `haff` (the affine-chart hypothesis): there is a subring $B \subseteq \mathrm{fieldBar}\,q\,M'$ containing the image of $A$, contained in $R.\mathrm{integers}$, contained in $S_x(Q)$ for every $Q \notin N$, and such that every $z \in F_{ss}$ lying in the valuation subring of every $Q \notin N$ is the $R$-residue of some element of $B$.
--
--   Under these hypotheses there exist $n \in \mathbb{N}$ and $g : \mathrm{Fin}\,n \to \mathrm{fieldBar}\,q\,M'$ with $g_i \in R.\mathrm{integers}$ for all $i$, such that: first, for every $i$, every place $Q \notin N$ and every $P \in D_x(Q)$, the function $g_i$ lies in the valuation subring of $P$ and $P.\mathrm{evalAt}(g_i) \in A$; and second, every $f \in F_{ss}$ lying in the valuation subring of every place $Q \notin N$ belongs to the $\kappa$-subalgebra of $F_{ss}$ generated by the $R$-residues of the $g_i$.
--
--   This is the case $q = 3$, at an auxiliary level rigidified by a prime $\ell \equiv 11 \pmod{12}$ dividing $M'$, of the statement that the ring of functions on the supersingular component of the semistable model which are regular away from the $q+1$ ends is generated, over the residue field of $A$, by reductions of finitely many functions on the full-level curve that are integral for the prolongation $R$ and regular with $A$-integral values on all the smooth residue discs. It is used in the analysis of the inertia action on the level orbits of the Drinfeld quotient describing the supersingular component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_exists_generators_regular_off_ends_of_affineChart_of_eq_three_of_dvd.lean

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

theorem ModularCurve.FullLevel.supersingularProlongation_exists_generators_regular_off_ends_of_affineChart_of_eq_three_of_dvd
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

    (hdl : (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
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

    (haff : ∃ B : Subring ↥(fieldBar q M'),

        (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ B) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ R.integers) ∧

        (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ Sx Q) ∧

        (∀ z : FSS, (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → z ∈ Q.toValuationSubring) →
          ∃ (f : ↥(fieldBar q M')) (_ : f ∈ B) (hfR : f ∈ R.integers), R.residue ⟨f, hfR⟩ = z)) :
        (∃ (n : ℕ) (g : Fin n → ↥(fieldBar q M')) (hg : ∀ i, g i ∈ R.integers),
          (∀ i, ∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P ∈ Dx Q,
            g i ∈ P.toValuationSubring ∧ P.evalAt (g i) ∈ A) ∧
          ∀ f : FSS, (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → f ∈ Q.toValuationSubring) →
            f ∈ Algebra.adjoin (ResidueField ↥A) (Set.range fun i => R.residue ⟨g i, hg i⟩)) := by sorry
