-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_exists_generators_regular_off_ends_of_affineChart
-- name    : ModularCurve.FullLevel.supersingularProlongation_exists_generators_regular_off_ends_of_affineChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/863347d7-3050-52be-a73a-ad029feb32d2
-- title:
--   R-integral generators regular off the ends, from an affine chart
-- statement:
--   Setting. Let $q$ be a prime with $5 \le q$ (`hq`) and let $M'$ be a non-zero natural number with $q \nmid M'$ (`hqM'`). Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with `A.LiesOverPrime q`, that is, $q$ is a non-unit of $A$ (`hA`); write $\kappa =$ `ResidueField A`. Let $W$ be a finite set of places of the field $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ (the intermediate field of $\kappa((q))$ generated over $\kappa$ by the reduced $j$-series `jqModC` and its $M'$-fold expansion) whose members are exactly the supersingular places in the sense of `ssPlaces q M' κ`, i.e. rational affine geometric places whose value at `jGeomGen` lies in `ssJSet q κ` (`hW`), and let $s$ be a chosen element of $W$. Let `hle` be the inclusion $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ of intermediate fields of $\overline{\mathbb Q}((q))$, the first obtained from the full modular function field of level $M'$ by base change of Laurent coefficients, the second the base-changed function field of the curve $X_H$ of level $q^2M'$ for $H =$ `levelH q M'`.
--
--   Let $R_0$ be a `ConstantReduction` of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}\,\kappa\,M'$: a valuation subring $R_0.\mathrm{integers}$ together with a surjective residue homomorphism onto $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ with kernel the maximal ideal, meeting $\overline{\mathbb Q}$ exactly in $A$ and inducing the residue map of $A$ there, with the scaling property for non-zero elements, and with a map on places preserving degrees and carrying principal divisors to orders of residues. The hypothesis `hR₀` states that for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb Q}((q))$ lies in $\mathrm{modularFunctionFieldBar}\,M'$, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$ along $A \to \kappa$.
--
--   Let $\mathrm{FSS}$ be a field that is a $\kappa$-algebra, and let $R$ be a `RegularProlongation` of $A$ from $\mathrm{fieldBar}\,q\,M'$ with residue field $\mathrm{FSS}$: a valuation subring $R.\mathrm{integers}$ with a surjective residue map onto $\mathrm{FSS}$ whose kernel is the maximal ideal, meeting $\overline{\mathbb Q}$ exactly in $A$, inducing the residue map of $A$, and with the scaling property. Let $N$ be a finite set of places of $\mathrm{FSS}$ over $\kappa$ (the ends), and let $Q \mapsto S_Q$, $Q \mapsto \varphi_Q : A[X] \to S_Q$, $Q \mapsto \chi_{0,Q} : S_Q \to \kappa$ and $Q \mapsto D_Q$ be families indexed by the places of $\mathrm{FSS}$ over $\kappa$, where $S_Q$ is a subring of $\mathrm{fieldBar}\,q\,M'$ and $D_Q$ a set of places of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb Q}$.
--
--   Hypotheses. `h0`: $\mathrm{FSS}$ contains an element transcendental over $\kappa$. `h1`: for every $f \in R_0.\mathrm{integers}$ whose order is non-negative at every place of $\mathrm{modularFunctionFieldBar}\,M'$ at which the transported $j$-series `coeffEmb _ jq` has non-negative order, and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $R.\mathrm{integers}$ and its $R$-residue is the image under $\kappa \to \mathrm{FSS}$ of the value at $s$ of the $R_0$-residue of $f$. `h2`: for every $\zeta \in \mathrm{Idx}\,q$ and every $\gamma \in \Gamma_0(M') \subset \mathrm{SL}_2(\mathbb Z)$, the pullback of $R.\mathrm{integers}$ along `levelAutBar q M' ζ γ` is $R.\mathrm{integers}$. `hcard`: $N$ has exactly $q+1$ elements.
--
--   `hpkg` (the smooth-point packages; fourteen clauses, summarised here) requires, for every place $Q \notin N$: the image of $A$ lies in $S_Q$; $\varphi_Q$ is formally smooth and formally unramified; $\varphi_Q(C\,a)$ is the image of $a$ for $a \in A$, and $\chi_{0,Q}(\varphi_Q(C\,a))$ is the residue of $a$, while $\chi_{0,Q}(\varphi_Q X) = 0$; for each $c \in A$ with residue $0$ there is a unique ring homomorphism $\chi : S_Q \to A$ splitting $\varphi_Q \circ C$, reducing to $\chi_{0,Q}$ and sending $\varphi_Q X$ to $c$; every $f \in S_Q$ is $R$-integral with $R$-residue in the valuation subring of $Q$, whose $Q$-residue is the image of $\chi_{0,Q}(f)$; $\varphi_Q X$ is $R$-integral and its $R$-residue has $Q$-order $1$; $D_Q$ consists exactly of the rational places $P$ at which every $f \in S_Q$ is integral with $P$-value in $A$ and for which $A$-valuation of $P.\mathrm{evalAt}(f) < 1$ holds precisely when $\chi_{0,Q}(f) = 0$; each $A$-point $\chi$ of $S_Q$ splitting $\varphi_Q \circ C$ and reducing to $\chi_{0,Q}$ is realised by a unique $P \in D_Q$ with $P.\mathrm{evalAt}(f) = \chi(f)$ for all $f \in S_Q$; for $P \in D_Q$ the valuation subring of $P$ consists of the quotients $g/h$ with $g, h \in S_Q$ and $P.\mathrm{evalAt}(h) \ne 0$; any non-zero $f$ with $P.\mathrm{ord}\,f = 0$ for all $P \in D_Q$ becomes a unit of $S_Q$ after multiplication by a non-zero constant of $\overline{\mathbb Q}$; and any $f \in R.\mathrm{integers}$ integral at all $P \in D_Q$ lies in $S_Q$.
--
--   `hdisj`: for $Q, Q' \notin N$, if some $P$ lies in both $D_Q$ and $D_{Q'}$ then $Q = Q'$. `hcusp`: for $Q \notin N$ and $P \in D_Q$, the order at $P$ of the image in $\mathrm{fieldBar}\,q\,M'$ of the transported $j$-series is non-negative. `heqv` (level stability): for every $\tau$ in the subgroup generated by the automorphisms `levelAutBar q M' ζ γ` with $\zeta \in \mathrm{Idx}\,q$ and $\gamma \in \Gamma_0(M')$, and for every proof $h_\tau$ that $\tau$ preserves $R.\mathrm{integers}$, the induced residual automorphism `R.resAut τ hτ` of $\mathrm{FSS}$ acts on places so that $Q$ lies in $N$ if and only if its translate does, and for $Q \notin N$ one has $\{P : \tau^{-1}\cdot P \in D_Q\} = D_{\mathrm{resAut}(\tau)\cdot Q}$. `hUniq` (uniqueness of packages): for $Q \notin N$, any quadruple $(S, \varphi, \chi_0, D)$ satisfying the same fourteen clauses at $Q$ has $D = D_Q$, $S = S_Q$ as subsets, and $\chi_0$ agreeing with $\chi_{0,Q}$ on common elements.
--
--   `hdl` (Drinfeld identification): for every $\mathbb F_{q^2}$-algebra structure on $\kappa$, every witness that $\mathrm{CoordRing}\,q\,\kappa$ is a domain and every $\zeta \in \mathrm{Idx}\,q$, there are a subgroup $C_s$ of the $(q+1)$-st roots of unity of $\mathbb F_{q^2}$ and a $\kappa$-algebra isomorphism $e$ from $\mathrm{FSS}$ onto the fixed field [`DrinfeldCurve.quotField q κ Cs`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) inside the Drinfeld function field, such that $\mathrm{card}\,C_s = 2\,\mathrm{placeWidthChar}\,q\,M'\,s$ and such that for every $\gamma \in \Gamma_0(M')$, given that `levelAutBar q M' ζ γ⁻¹` preserves $R.\mathrm{integers}$ and that $(\mathrm{redQ}\,q\,\gamma, 1)$ lies in [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276), the map $e$ intertwines the residual automorphism of $\mathrm{FSS}$ induced by `levelAutBar q M' ζ γ⁻¹` with the action of that element of the subgroup on the Drinfeld function field.
--
--   `haff` (the affine chart): there exists a subring $B$ of $\mathrm{fieldBar}\,q\,M'$ containing the image of $A$, contained in $R.\mathrm{integers}$, contained in $S_Q$ for every $Q \notin N$, and such that every $z \in \mathrm{FSS}$ lying in the valuation subring of every $Q \notin N$ is the $R$-residue of some element of $B$.
--
--   Conclusion. There exist a natural number $n$, a family $g : \mathrm{Fin}\,n \to \mathrm{fieldBar}\,q\,M'$ and proofs that each $g_i$ lies in $R.\mathrm{integers}$, such that: first, for every index $i$, every place $Q \notin N$ and every $P \in D_Q$, the element $g_i$ lies in the valuation subring of $P$ and its value $P.\mathrm{evalAt}(g_i)$ lies in $A$; second, every $f \in \mathrm{FSS}$ that lies in the valuation subring of every place $Q \notin N$ belongs to the $\kappa$-subalgebra of $\mathrm{FSS}$ generated by the $R$-residues of the $g_i$.
--
--   This is the step, in the analysis of the supersingular components of the special fibre of the modular curve of level $q^2M'$ over a valuation ring lying over $q$, that produces finitely many functions on the characteristic-zero curve which are $R$-integral, regular with $A$-integral values on all the smooth residue discs, and whose reductions generate the ring of functions on the supersingular component that are regular away from the $q+1$ ends. It is used by [`ModularCurve.FullLevel.supersingularProlongation_drinfeldQuotient_levelOrbits_generators_inertia_of_drinfeldIdentification_of_affineChart`](thm.html#ModularCurve.FullLevel.supersingularProlongation_drinfeldQuotient_levelOrbits_generators_inertia_of_drinfeldIdentification_of_affineChart), where such generators are combined with the Drinfeld identification to control the action of inertia on level orbits.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_exists_generators_regular_off_ends_of_affineChart.lean

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

theorem ModularCurve.FullLevel.supersingularProlongation_exists_generators_regular_off_ends_of_affineChart
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
        (∃ (n : ℕ) (g : Fin n → ↥(fieldBar q M')) (hg : ∀ i, g i ∈ R.integers),
          (∀ i, ∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P ∈ Dx Q,
            g i ∈ P.toValuationSubring ∧ P.evalAt (g i) ∈ A) ∧
          ∀ f : FSS, (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → f ∈ Q.toValuationSubring) →
            f ∈ Algebra.adjoin (ResidueField ↥A) (Set.range fun i => R.residue ⟨g i, hg i⟩)) := by sorry
