-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_exists_finite_generators_regular_off_ends_residueField
-- name    : ModularCurve.FullLevel.supersingularProlongation_exists_finite_generators_regular_off_ends_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/e1a57558-6259-5c24-95e8-8835c37c4b0a
-- title:
--   Finite generation of functions regular off the q+1 ends
-- statement:
--   Fix a prime $q \ge 5$ and a natural number $M' \neq 0$ with $q \nmid M'$. Let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` lying over $q$ in the sense of `LiesOverPrime`, i.e. $q$ is a non-unit of $A$ (hypothesis `hA`), and write $\kappa =$ `ResidueField A`. Let $W$ be a finite set of places of the field `modularFunctionFieldC κ M'` $= \kappa(j_q, j_{q,M'})$ over $\kappa$ which, by `hW`, consists exactly of the members of `ssPlaces q M' κ`: the places $w$ that are rational (the residue map $\kappa \to w.\mathrm{ResidueField}$ is surjective), satisfy the predicate `IsAffineGeomPlace`, and have $w.\mathrm{evalAt}\,(\mathrm{jGeomGen}\ \kappa\ M') \in \mathrm{ssJSet}\ q\ \kappa$. Hypothesis `hle` records the inclusion `modularFunctionFieldBar M'` $\le$ `fieldBar q M'` of intermediate fields of $\overline{\mathbb Q} \subseteq \overline{\mathbb Q}((t))$, the former being the base change to $\overline{\mathbb Q}$ of the full level-$M'$ modular function field, the latter the base change of the function field of the $H$-quotient at level $q^2M'$ for $H =$ `levelH q M'`.
--
--   The reduction data at level $M'$ consist of a `ConstantReduction` $R_0$ of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'` — a valuation subring $R_0.\mathrm{integers}$, a surjective residue homomorphism onto `modularFunctionFieldC κ M'` with kernel the maximal ideal, the conditions that $\mathrm{algebraMap}\,x$ lies in $R_0.\mathrm{integers}$ exactly when $x \in A$ and that the residue of a constant is its reduction, the scaling property that every nonzero $f$ can be multiplied by a constant so as to become integral with nonzero residue, and a degree- and order-preserving map on places — together with the compatibility `hR₀`: for every Laurent series $y$ with coefficients in $A$ whose image under $\mathrm{coeffMap}$ of the inclusion $A \hookrightarrow \overline{\mathbb Q}$ lies in `modularFunctionFieldBar M'`, that image is $R_0$-integral and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction $\mathrm{coeffMap}\,(\mathrm{residue}\ A)\,y$. An element $s$ of $W$ is fixed, i.e. a supersingular place in the above sense.
--
--   The reduction data at full level consist of a field $FSS$ with a $\kappa$-algebra structure and a `RegularProlongation` $R$ of $A$ from `fieldBar q M'` to $FSS$ (a valuation subring $R.\mathrm{integers}$ of `fieldBar q M'`, a surjective residue homomorphism onto $FSS$ with kernel the maximal ideal, the same compatibility with $A$, the same rule for residues of constants, and the same scaling property), a finite set $N$ of places of $FSS$ over $\kappa$, and, for every place $Q$ of $FSS$ over $\kappa$, a subring $Sx\,Q$ of `fieldBar q M'`, a ring homomorphism $\varphi x\,Q : A[X] \to Sx\,Q$, a ring homomorphism $\chi_0x\,Q : Sx\,Q \to \kappa$, and a set $Dx\,Q$ of places of `fieldBar q M'` over $\overline{\mathbb Q}$.
--
--   The hypotheses on these data are the following. `h0`: some element of $FSS$ is transcendental over $\kappa$. `h1`: for every $f \in R_0.\mathrm{integers}$ such that $f$ is regular at every place $P$ of `modularFunctionFieldBar M'` over $\overline{\mathbb Q}$ at which the element $j_q$ of `modularFunctionFieldBar M'` (the Laurent series `jq` with coefficients pushed into $\overline{\mathbb Q}$) is regular, and such that $R_0.\mathrm{residue}\,f$ lies in the valuation subring of $s$, the image of $f$ in `fieldBar q M'` under the inclusion `hle` lies in $R.\mathrm{integers}$ and its $R$-residue is the image in $FSS$ of $s.\mathrm{evalAt}(R_0.\mathrm{residue}\,f)$. `h2`: for every $\zeta$ in `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb Q}$) and every $\gamma \in \Gamma_0(M') \subseteq \mathrm{SL}_2(\mathbb Z)$, the pullback of $R.\mathrm{integers}$ along the level automorphism `levelAutBar q M' ζ γ` equals $R.\mathrm{integers}$. `hcard`: $N$ has exactly $q+1$ elements.
--
--   `hpkg` is a smooth-point package at each place $Q \notin N$, asserting thirteen clauses: the image of $A$ in `fieldBar q M'` is contained in $Sx\,Q$; $\varphi x\,Q$ is formally smooth and formally unramified; $\varphi x\,Q(C\,a)$ is the image of $a$ for every $a \in A$; $\chi_0x\,Q(\varphi x\,Q(C\,a))$ is the residue of $a$; $\chi_0x\,Q(\varphi x\,Q(X)) = 0$; for every $c \in A$ with zero residue there is a unique ring homomorphism $\chi : Sx\,Q \to A$ splitting $\varphi x\,Q \circ C$, lifting $\chi_0x\,Q$ (the residue of $\chi f$ is $\chi_0x\,Q f$) and sending $\varphi x\,Q(X)$ to $c$; every $f \in Sx\,Q$ lies in $R.\mathrm{integers}$, its $R$-residue lies in the valuation subring of $Q$, and the residue there equals the image of $\chi_0x\,Q f$ in $Q.\mathrm{ResidueField}$; $\varphi x\,Q(X)$ is $R$-integral and its $R$-residue has $Q$-order $1$; $Dx\,Q$ consists precisely of the rational places $P$ of `fieldBar q M'` over $\overline{\mathbb Q}$ such that every $f \in Sx\,Q$ is $P$-integral with $P.\mathrm{evalAt}\,f \in A$, and such that $A$-valuation of $P.\mathrm{evalAt}\,f$ is $<1$ exactly when $\chi_0x\,Q f = 0$; every $\chi : Sx\,Q \to A$ splitting $\varphi x\,Q \circ C$ and lifting $\chi_0x\,Q$ is realised by a unique $P \in Dx\,Q$ via $P.\mathrm{evalAt} = \chi$ on $Sx\,Q$; for $P \in Dx\,Q$, an element $f$ of `fieldBar q M'` is $P$-integral exactly when $f h = g$ for some $g, h \in Sx\,Q$ with $P.\mathrm{evalAt}\,h \neq 0$; every nonzero $f$ with $P.\mathrm{ord}\,f = 0$ for all $P \in Dx\,Q$ becomes, after multiplication by a nonzero constant of $\overline{\mathbb Q}$, a unit of $Sx\,Q$; and every $f \in R.\mathrm{integers}$ that is $P$-integral for all $P \in Dx\,Q$ lies in $Sx\,Q$.
--
--   `hdisj`: for $Q, Q' \notin N$ the discs $Dx\,Q$ and $Dx\,Q'$ are disjoint unless $Q = Q'$. `hcusp`: for $Q \notin N$ and $P \in Dx\,Q$, the image of $j_q$ in `fieldBar q M'` is regular at $P$. `heqv`: for every $\tau$ in the subgroup of $\overline{\mathbb Q}$-automorphisms of `fieldBar q M'` generated by the automorphisms `levelAutBar q M' ζ γ` with $\zeta \in$ `Idx q` and $\gamma \in \Gamma_0(M')$, and given that $\tau$ preserves $R.\mathrm{integers}$, the induced automorphism $R.\mathrm{resAut}\,\tau$ of $FSS$ over $\kappa$ preserves $N$ (a place $Q$ lies in $N$ iff its translate does) and, for $Q \notin N$, carries discs to discs in the sense $\mathrm{smulDisc}\,\tau\,(Dx\,Q) = Dx(R.\mathrm{resAut}\,\tau \cdot Q)$, where $\mathrm{smulDisc}\,\tau\,D = \{P : \tau^{-1} \cdot P \in D\}$. `hUniq`: the package is unique, namely for $Q \notin N$ any quadruple $(S, \varphi, \chi_0, D)$ satisfying the same thirteen clauses satisfies $D = Dx\,Q$, $S = Sx\,Q$ and $\chi_0 = \chi_0x\,Q$ on common elements.
--
--   `hdl` is the Drinfeld identification: for every $\mathbb F_{q^2}$-algebra structure on $\kappa$ (via `GaloisField q 2`), assuming [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain, and for every $\zeta \in$ `Idx q`, there are a subgroup $C_s$ of the $(q+1)$-st roots of unity of $\mathbb F_{q^2}$ and a $\kappa$-algebra isomorphism $e$ from $FSS$ onto [`DrinfeldCurve.quotField q κ Cs`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32), the subfield of the Drinfeld function field over $\kappa$ fixed by the subgroup generated by the actions of $C_s$, such that $\mathrm{Nat.card}\,C_s = 2\,\cdot$ `placeWidthChar q M' s` and such that $e$ is equivariant: for $\gamma \in \Gamma_0(M')$ with `levelAutBar q M' ζ γ⁻¹` preserving $R.\mathrm{integers}$, and with $(\mathrm{redQ}\,q\,\gamma, 1)$ lying in [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276), the automorphism $R.\mathrm{resAut}$ of that level automorphism is transported by $e$ to the action `hFunctionFieldAction` of $(\mathrm{redQ}\,q\,\gamma, 1)$ on the Drinfeld function field.
--
--   Under these hypotheses the conclusion asserts the existence of a natural number $n$ and a family $z : \mathrm{Fin}\,n \to FSS$ such that: first, every $z\,i$ lies in the valuation subring of every place $Q$ of $FSS$ over $\kappa$ with $Q \notin N$; and second, every $f \in FSS$ that lies in the valuation subring of every place $Q \notin N$ belongs to the $\kappa$-subalgebra $\mathrm{Algebra.adjoin}\,\kappa\,(\mathrm{Set.range}\,z)$ generated by the $z\,i$.
--
--   This is the finite-generation step in the analysis of the supersingular fibres of the semistable model of the modular curve of level $q^2M'$: via the Drinfeld (Deligne–Lusztig) identification of the reduced function field $FSS$, the $q+1$ places in $N$ are the ends of the quotient Drinfeld curve and the functions regular away from them form a finitely generated $\kappa$-algebra. It is used by [`ModularCurve.FullLevel.supersingularProlongation_exists_generators_regular_off_ends_of_affineChart`](thm.html#ModularCurve.FullLevel.supersingularProlongation_exists_generators_regular_off_ends_of_affineChart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_exists_finite_generators_regular_off_ends_residueField.lean

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

theorem ModularCurve.FullLevel.supersingularProlongation_exists_finite_generators_regular_off_ends_residueField
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
                    DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))))) :
        (∃ (n : ℕ) (z : Fin n → FSS),
          (∀ i, ∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → z i ∈ Q.toValuationSubring) ∧
          ∀ f : FSS, (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → f ∈ Q.toValuationSubring) →
            f ∈ Algebra.adjoin (ResidueField ↥A) (Set.range z)) := by sorry
