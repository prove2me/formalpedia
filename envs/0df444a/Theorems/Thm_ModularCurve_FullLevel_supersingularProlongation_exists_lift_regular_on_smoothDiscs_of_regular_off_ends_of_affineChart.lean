-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_exists_lift_regular_on_smoothDiscs_of_regular_off_ends_of_affineChart
-- name    : ModularCurve.FullLevel.supersingularProlongation_exists_lift_regular_on_smoothDiscs_of_regular_off_ends_of_affineChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/312fb81e-ce92-5130-be90-319ad8212265
-- title:
--   Lifting functions regular off the ends, given an affine chart
-- statement:
--   Throughout, $\bar{\mathbb Q}$ denotes `AlgebraicClosure ℚ`, and `Place K F` is the structure consisting of a valuation subring of $F$ containing the image of $K$, different from $F$, whose underlying ring is a principal ideal ring; for such a place $P$, $P.\mathrm{ord}$ is minus the logarithm of the associated $\mathbb Z^{m0}$-valued adic valuation, $P$ is *rational* when $K$ surjects onto its residue field, and $P.\mathrm{evalAt}\,f$ is the element of $K$ corresponding to the residue of $f$ when $f$ lies in the valuation subring of $P$, and $0$ otherwise.
--
--   **Data.** A prime $q$ with $5 \le q$; a nonzero natural number $M'$ with $q \nmid M'$; a valuation subring $A$ of $\bar{\mathbb Q}$ with $q$ a non-unit of $A$ (the predicate [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16)); a finite set $W$ of places of the characteristic-$p$ modular function field $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M') = \kappa(j_q, j_{q,M'})$ over $\kappa := \mathrm{ResidueField}\,A$, with `hW` asserting that $W$ consists exactly of the supersingular places, i.e. the places $w$ which are rational, are affine geometric places, and satisfy $w.\mathrm{evalAt}(\mathrm{jGeomGen}\,\kappa\,M') \in \mathrm{ssJSet}\,q\,\kappa$; a hypothesis `hle` that the base change $\mathrm{modularFunctionFieldBar}\,M'$ to $\bar{\mathbb Q}$ of the full-level modular function field of level $M'$ is contained, inside $\mathrm{LaurentSeries}\,\bar{\mathbb Q}$, in $\mathrm{fieldBar}\,q\,M'$, the base change of the $X_H$-function field of level $q^2M'$ for $H = \mathrm{levelH}\,q\,M'$; a constant reduction $R_0$ of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ (a valuation subring $R_0.\mathrm{integers}$, a surjective residue map with kernel the maximal ideal, compatible with $A$ and inducing a degree-preserving map on places); the hypothesis `hR₀` that for every Laurent series $y$ with coefficients in $A$ whose image in $\mathrm{LaurentSeries}\,\bar{\mathbb Q}$ lies in $\mathrm{modularFunctionFieldBar}\,M'$, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$; and a chosen element $s \in W$.
--
--   Further, a field $FSS$ with a $\kappa$-algebra structure; a regular prolongation $R$ of $A$ from $\mathrm{fieldBar}\,q\,M'$ to $FSS$ (a valuation subring $R.\mathrm{integers}$ with surjective residue map onto $FSS$ whose kernel is the maximal ideal, restricting to $A$ on constants, compatible with the residue map of $A$, and such that every nonzero $f$ can be scaled by a constant into $R.\mathrm{integers}$ with nonzero residue); a finite set $N$ of places of $FSS$ over $\kappa$ (the ends); and, indexed by the places $Q$ of $FSS$ over $\kappa$, a subring $S_Q := Sx\,Q$ of $\mathrm{fieldBar}\,q\,M'$, a ring homomorphism $\varphi_Q := φx\,Q$ from $A[X]$ to $S_Q$, a ring homomorphism $\chi_{0,Q} := χ₀x\,Q$ from $S_Q$ to $\kappa$, and a set $D_Q := Dx\,Q$ of places of $\mathrm{fieldBar}\,q\,M'$ over $\bar{\mathbb Q}$.
--
--   **Hypotheses.** `h0`: some element of $FSS$ is transcendental over $\kappa$. `h1` (compatibility of $R$ with $R_0$ at $s$): for every $f \in R_0.\mathrm{integers}$ such that non-negativity of $P.\mathrm{ord}$ at the image of the $q$-expansion $j_q$ implies non-negativity of $P.\mathrm{ord}\,f$ for every place $P$ of $\mathrm{modularFunctionFieldBar}\,M'$ over $\bar{\mathbb Q}$, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $R.\mathrm{integers}$ and its $R$-residue is the image under $\kappa \to FSS$ of $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$. `h2` (level stability): for every $\zeta \in \mathrm{Idx}\,q$ and every $\gamma \in \Gamma_0(M')$ in $\mathrm{SL}_2(\mathbb Z)$, the preimage of $R.\mathrm{integers}$ under $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ is $R.\mathrm{integers}$. `hcard`: $N$ has exactly $q+1$ elements.
--
--   `hpkg` (the smooth-point packages; fourteen clauses, summarised here): for each place $Q \notin N$, the constants from $A$ lie in $S_Q$; $\varphi_Q$ is formally smooth and formally unramified; $\varphi_Q$ sends $C\,a$ to the image of $a$ and $\chi_{0,Q}(\varphi_Q(C\,a))$ is the residue of $a$, while $\chi_{0,Q}(\varphi_Q X) = 0$; for each $c \in A$ with residue $0$ there is a unique ring homomorphism $\chi : S_Q \to A$ which is the identity on constants, lifts $\chi_{0,Q}$, and sends $\varphi_Q X$ to $c$; every $f \in S_Q$ lies in $R.\mathrm{integers}$, its $R$-residue lies in the valuation subring of $Q$ and has residue there the image of $\chi_{0,Q} f$; the $R$-residue of $\varphi_Q X$ has $Q$-order $1$; $D_Q$ consists exactly of the rational places $P$ of $\mathrm{fieldBar}\,q\,M'$ over $\bar{\mathbb Q}$ at which every $f \in S_Q$ is integral with $P.\mathrm{evalAt}\,f \in A$, and for which $A$-valuation of $P.\mathrm{evalAt}\,f$ is $<1$ precisely when $\chi_{0,Q} f = 0$; every $A$-point $\chi$ of $S_Q$ lifting $\chi_{0,Q}$ and fixing the constants is realised by a unique $P \in D_Q$ via $P.\mathrm{evalAt}$; for $P \in D_Q$, membership of $f$ in the valuation subring of $P$ is equivalent to $f$ being a quotient $g/h$ with $g,h \in S_Q$ and $P.\mathrm{evalAt}\,h \ne 0$; a unit principle, namely any nonzero $f$ with $P.\mathrm{ord}\,f = 0$ for all $P \in D_Q$ becomes a unit of $S_Q$ after multiplication by a nonzero constant; and any $f \in R.\mathrm{integers}$ integral at all $P \in D_Q$ lies in $S_Q$.
--
--   `hdisj`: for $Q, Q' \notin N$, if some place lies in both $D_Q$ and $D_{Q'}$ then $Q = Q'$. `hcusp`: for $Q \notin N$ and $P \in D_Q$, $P.\mathrm{ord}$ of the image in $\mathrm{fieldBar}\,q\,M'$ of $j_q$ is non-negative. `heqv` (equivariance): for every $\tau$ in the subgroup of $\bar{\mathbb Q}$-automorphisms of $\mathrm{fieldBar}\,q\,M'$ generated by the $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ with $\gamma \in \Gamma_0(M')$, and every proof that $\tau$ preserves $R.\mathrm{integers}$, the induced residual automorphism $R.\mathrm{resAut}\,\tau$ preserves $N$ under its action on places, and for $Q \notin N$ it carries the discs along: $\{P \mid \tau^{-1} \cdot P \in D_Q\} = D_{R.\mathrm{resAut}\,\tau \cdot Q}$.
--
--   `hUniq` (uniqueness of packages): for $Q \notin N$, any quadruple $(S, \varphi, \chi_0, D)$ satisfying the same fourteen clauses as in `hpkg` has $D = D_Q$ and $S = S_Q$ as sets, and $\chi_0$ agrees with $\chi_{0,Q}$ on common elements.
--
--   `hdl` (Drinfeld identification): for every $\mathrm{GaloisField}\,q\,2$-algebra structure on $\kappa$, assuming $\mathrm{CoordRing}\,q\,\kappa$ is a domain, and for every $\zeta \in \mathrm{Idx}\,q$, there are a subgroup $C_s$ of the group of $(q+1)$-st roots of unity in $\mathrm{GaloisField}\,q\,2$ and a $\kappa$-algebra isomorphism $e$ from $FSS$ to the fixed field $\mathrm{quotField}\,q\,\kappa\,C_s$ inside the Drinfeld function field, such that $\#C_s = 2\,\mathrm{placeWidthChar}\,q\,M'\,s$ and such that, for $\gamma \in \Gamma_0(M')$ with the relevant compatibilities, $e$ intertwines the residual automorphism induced by $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma^{-1}$ with the action of $(\mathrm{redQ}\,q\,\gamma, 1)$ through $\mathrm{hFunctionFieldAction}$.
--
--   `haff` (affine chart, the hypothesis distinguishing this statement): there exists a subring $B$ of $\mathrm{fieldBar}\,q\,M'$ such that the constants from $A$ lie in $B$; every element of $B$ lies in $R.\mathrm{integers}$; for every $Q \notin N$ every element of $B$ lies in $S_Q$; and every $z \in FSS$ which lies in the valuation subring of every place $Q \notin N$ is the $R$-residue of some element of $B$.
--
--   **Conclusion.** For every $z \in FSS$ lying in the valuation subring of every place $Q \notin N$, there exist $g \in \mathrm{fieldBar}\,q\,M'$ and a proof that $g \in R.\mathrm{integers}$ such that: the $R$-residue of $g$ equals $z$; and for every place $Q \notin N$ and every $P \in D_Q$, $g$ lies in the valuation subring of $P$ and $P.\mathrm{evalAt}\,g \in A$.
--
--   This is a step in the analysis of the special fibre of the modular curve of level $q^2M'$ over a valuation ring of $\bar{\mathbb Q}$ above $q$: it upgrades a function on the supersingular component that is regular away from the $q+1$ ends to an $R$-integral lift which is, in addition, regular with $A$-integral values on every smooth residue disc. The existence of an $A$-integral affine chart inside all the smooth-point packages with surjective reduction is taken as a hypothesis here; the result is used by [`ModularCurve.FullLevel.supersingularProlongation_exists_generators_regular_off_ends_of_affineChart`](thm.html#ModularCurve.FullLevel.supersingularProlongation_exists_generators_regular_off_ends_of_affineChart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_exists_lift_regular_on_smoothDiscs_of_regular_off_ends_of_affineChart.lean

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

theorem ModularCurve.FullLevel.supersingularProlongation_exists_lift_regular_on_smoothDiscs_of_regular_off_ends_of_affineChart
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
                    DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))))

    (haff : ∃ B : Subring ↥(fieldBar q M'),

        (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ B) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ R.integers) ∧

        (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ Sx Q) ∧

        (∀ z : FSS, (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → z ∈ Q.toValuationSubring) →
          ∃ (f : ↥(fieldBar q M')) (_ : f ∈ B) (hfR : f ∈ R.integers), R.residue ⟨f, hfR⟩ = z)) :
        (∀ z : FSS, (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → z ∈ Q.toValuationSubring) →
          ∃ (g : ↥(fieldBar q M')) (hg : g ∈ R.integers), R.residue ⟨g, hg⟩ = z ∧
            ∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P ∈ Dx Q,
              g ∈ P.toValuationSubring ∧ P.evalAt g ∈ A) := by sorry
