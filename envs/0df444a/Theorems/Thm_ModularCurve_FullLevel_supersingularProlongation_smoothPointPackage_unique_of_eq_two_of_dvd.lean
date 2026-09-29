-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_unique_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.supersingularProlongation_smoothPointPackage_unique_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/cfd9749a-d7bb-503f-9720-04a33955421f
-- title:
--   Uniqueness of smooth-point packages on the supersingular component, q=2
-- statement:
--   Fix a prime $q$ together with the hypothesis `hq2` that $q = 2$, a nonzero level $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Fix a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ is a non-unit of $A$, and write $\kappa =$ `ResidueField A`. A finite set $W$ of places of `modularFunctionFieldC` $\kappa\,M'$ over $\kappa$ is given, and the hypothesis `hW` says that $W$ is exactly `ssPlaces q M' κ`, i.e. the set of places $w$ that are rational, satisfy the predicate `IsAffineGeomPlace`, and whose evaluation at `jGeomGen κ M'` lies in `ssJSet q κ`; $s$ is an element of $W$. The hypothesis `hle` provides the inclusion `modularFunctionFieldBar M'` $\le$ `fieldBar q M'` of intermediate fields of `LaurentSeries` $\overline{\mathbb{Q}}$, the former being the base change to $\overline{\mathbb{Q}}$ of the level-$M'$ full modular function field, the latter that of the $X_H$-function field of level $q^2M'$ for $H =$ `levelH q M'`.
--
--   The datum $R_0$ is a `ConstantReduction` of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'`: a valuation subring $R_0.\mathrm{integers}$, a surjective residue homomorphism onto `modularFunctionFieldC κ M'` with kernel the maximal ideal, compatible with $A$ and with $\mathrm{residue}_A$, satisfying the scaling property, together with a map on places preserving degrees and compatible with divisors of functions. The hypothesis `hR₀` states that $R_0$ computes coefficientwise reduction: for every Laurent series $y$ with coefficients in $A$ whose image under `coeffMap A.subtype` lies in `modularFunctionFieldBar M'`, that image lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise residue of $y$.
--
--   Further data: a field $FSS$ over $\kappa$ and a `RegularProlongation` $R$ of $A$ from `fieldBar q M'` to $FSS$ (a valuation subring $R.\mathrm{integers}$ with surjective residue map onto $FSS$, kernel the maximal ideal, compatible with $A$, and satisfying the scaling property); a finite set $N$ of places of $FSS$ over $\kappa$; and, indexed by places $Q$ of $FSS$ over $\kappa$, a subring $S_x(Q)$ of `fieldBar q M'`, a ring homomorphism $\varphi_x(Q) \colon A[T] \to S_x(Q)$, a ring homomorphism $\chi_{0x}(Q) \colon S_x(Q) \to \kappa$, and a set $D_x(Q)$ of places of `fieldBar q M'` over $\overline{\mathbb{Q}}$.
--
--   The hypotheses on these data are: `h0`, that $FSS$ contains an element transcendental over $\kappa$; `h1`, that for every $f \in R_0.\mathrm{integers}$ whose order is nonnegative at every place of `modularFunctionFieldBar M'` at which the $q$-expansion `coeffEmb` $\overline{\mathbb{Q}}$ `jq` of $j$ has nonnegative order, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in `fieldBar q M'` lies in $R.\mathrm{integers}$ and its $R$-residue is the image in $FSS$ of the value at $s$ of that $R_0$-residue; `h2`, that $R.\mathrm{integers}$ is invariant under `levelAutBar q M' ζ γ` for every $\zeta \in$ `Idx q` and every $\gamma \in \Gamma_0(M')$; and `hcard`, that $N$ has exactly $q+1$ elements.
--
--   The hypothesis `hpkg` requires, for every place $Q \notin N$, fourteen clauses for the quadruple $(S_x(Q), \varphi_x(Q), \chi_{0x}(Q), D_x(Q))$: the image of $A$ in `fieldBar q M'` lies in $S_x(Q)$; $\varphi_x(Q)$ is formally smooth and formally unramified; $\varphi_x(Q)(C a)$ is the image of $a$ for $a \in A$, and $\chi_{0x}(Q)(\varphi_x(Q)(C a)) = \mathrm{residue}_A(a)$; $\chi_{0x}(Q)(\varphi_x(Q)(T)) = 0$; for every $c \in A$ of residue $0$ there is a unique ring homomorphism $\chi \colon S_x(Q) \to A$ splitting $A \to S_x(Q)$, lifting $\chi_{0x}(Q)$, and sending $\varphi_x(Q)(T)$ to $c$; every $f \in S_x(Q)$ lies in $R.\mathrm{integers}$, its $R$-residue lies in the valuation subring of $Q$, and the residue of the latter in $Q.\mathrm{ResidueField}$ is the image of $\chi_{0x}(Q)(f)$; the $R$-residue of $\varphi_x(Q)(T)$ has order $1$ at $Q$; $D_x(Q)$ consists exactly of the rational places $P$ of `fieldBar q M'` over $\overline{\mathbb{Q}}$ such that every $f \in S_x(Q)$ lies in the valuation subring of $P$ with $P.\mathrm{evalAt}(f) \in A$, and such that $A$-valuation of $P.\mathrm{evalAt}(f)$ is $< 1$ precisely when $\chi_{0x}(Q)(f) = 0$; every $A$-section $\chi$ of $S_x(Q)$ lifting $\chi_{0x}(Q)$ is realised by a unique $P \in D_x(Q)$ with $P.\mathrm{evalAt}(f) = \chi(f)$ for all $f$; for $P \in D_x(Q)$, membership of $f$ in the valuation subring of $P$ is equivalent to $f$ being a quotient of elements of $S_x(Q)$ with denominator of nonzero value at $P$; a nonzero $f$ of order $0$ at every $P \in D_x(Q)$ becomes, after multiplication by a nonzero constant of $\overline{\mathbb{Q}}$, a unit of $S_x(Q)$; and every $f \in R.\mathrm{integers}$ lying in the valuation subring of every $P \in D_x(Q)$ lies in $S_x(Q)$.
--
--   Three further hypotheses constrain the family of discs: `hdisj`, that the discs of distinct places outside $N$ are disjoint (a place lying in $D_x(Q)$ and $D_x(Q')$ for $Q, Q' \notin N$ forces $Q = Q'$); `hcusp`, that for $Q \notin N$ the image of `coeffEmb` $\overline{\mathbb{Q}}$ `jq` in `fieldBar q M'` has nonnegative order at every $P \in D_x(Q)$; and `heqv`, that for every $\tau$ in the subgroup generated by the automorphisms `levelAutBar q M' ζ γ` with $\zeta \in$ `Idx q` and $\gamma \in \Gamma_0(M')$ which preserves $R.\mathrm{integers}$, the induced residue automorphism `R.resAut` permutes $N$ (that is, $\tau$-translate of $Q$ lies in $N$ iff $Q$ does) and carries discs to discs: for $Q \notin N$, `RegularProlongation.smulDisc` $\tau\,(D_x(Q)) = D_x(\mathrm{resAut}(\tau) \cdot Q)$.
--
--   The conclusion is a uniqueness assertion. For every place $Q \notin N$ and every quadruple consisting of a subring $S$ of `fieldBar q M'`, a ring homomorphism $\varphi \colon A[T] \to S$, a ring homomorphism $\chi_0 \colon S \to \kappa$ and a set $D$ of places of `fieldBar q M'` over $\overline{\mathbb{Q}}$ satisfying the same fourteen clauses relative to $R$ and $Q$ (the clauses listed above, with $(S, \varphi, \chi_0, D)$ in place of $(S_x(Q), \varphi_x(Q), \chi_{0x}(Q), D_x(Q))$), the following three statements hold: a place $P$ of `fieldBar q M'` over $\overline{\mathbb{Q}}$ lies in $D$ if and only if it lies in $D_x(Q)$; an element $f$ of `fieldBar q M'` lies in $S$ if and only if it lies in $S_x(Q)$; and for every $f$ belonging to both $S$ and $S_x(Q)$, the values $\chi_0(f)$ and $\chi_{0x}(Q)(f)$ in $\kappa$ agree.
--
--   At a place $Q$ of the reduction of a regular prolongation lying over a supersingular point $s$, the étale coordinate ring, its residue character and its residue disc are determined by the prolongation and the place alone; this is the rigidity statement that makes data extracted from a chosen witness of the existence theorem for supersingular regular prolongations independent of the choice. It is used in assembling the semistable local model at level $q^2M'$ for $q = 2$ with the auxiliary level condition $\ell \equiv 11 \pmod{12}$, $\ell \mid M'$, and is cited by the corresponding existence statement for prolongations, smooth-point charts, node presentations and inertia data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_unique_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.supersingularProlongation_smoothPointPackage_unique_of_eq_two_of_dvd
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
            (Q ∉ N → AlgebraicCurve.RegularProlongation.smulDisc τ (Dx Q) = Dx (R.resAut τ hτ • Q)))) :
    (∀ Q ∉ N, ∀ (S : Subring ↥(fieldBar q M')) (φ : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A)
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
          (∀ (f : ↥(fieldBar q M')) (hf : f ∈ S) (hf' : f ∈ Sx Q), χ₀ ⟨f, hf⟩ = χ₀x Q ⟨f, hf'⟩)) := by sorry
