-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_smoothPointStalk_of_affineChart
-- name    : ModularCurve.FullLevel.supersingularProlongation_smoothPointStalk_of_affineChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/63cc95b0-918f-5ed7-a9c4-5a994c4a5fdd
-- title:
--   Étale coordinate and residue character on a smooth-point stalk
-- statement:
--   Fix a prime $q\ge 5$ and a nonzero natural number $M'$ with $q\nmid M'$, a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $q$ (i.e. the image of $q$ is a nonunit of $A$), a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,(\kappa(A))\,M'$ over $\kappa(A)=\mathrm{ResidueField}\,A$ whose members are exactly the supersingular places $\mathrm{ssPlaces}\;q\;M'\;\kappa(A)$, an element $s$ of $W$, the inclusion $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$ of intermediate fields of $\overline{\mathbb Q}((t))$ over $\overline{\mathbb Q}$, and a subfield $k_0\subseteq\overline{\mathbb Q}$ such that every $a\in A$ is congruent modulo $\mathfrak m_A$ to an element of $k_0\cap A$, with $\kappa(A)$ algebraically closed. Let $K_b$ be the trivial intermediate extension of $k_0$ in $\overline{\mathbb Q}$ and $A_b$ the valuation subring of $K_b$ cut out by $A$, assumed to be a henselian discrete valuation ring with nonzero uniformiser $\varpi_b$ generating its maximal ideal. The assertion is then: for every intermediate field $F_0$ of $\mathrm{fieldBar}\,q\,M'$ over $k_0$ and valuation subring $W_0$ of $F_0$ such that the compositum of $k_0(\overline{\mathbb Q})$ with $F_0$ is everything and $\overline{\mathbb Q}$ and $F_0$ are linearly disjoint over $k_0$ along finite layers (families $c_i$ linearly independent over a finite extension $K'/k_0$ annihilate only zero vectors with entries in $k_0(K')\sqcup F_0$), and for every subring $B$ of $\mathrm{fieldBar}\,q\,M'$ carrying an $A_b$-algebra structure compatible with the inclusions, with $B$ contained in the compositum $k_0(K_b)\sqcup F_0$ and having that compositum as fraction field, $B$ formally smooth and of finite presentation over $A_b$, $\mathrm{KrullDimLE}\;1$ for $B/\varpi_b B$, $B$ contained in $W_0$, $\varpi_b B$ prime, and $W_0$ the localisation of $B$ away from $\varpi_b$, and for every field $F_{ss}$ over $\kappa(A)$ with a regular prolongation $R$ of $A$ to $\mathrm{fieldBar}\,q\,M'$ with residue field target $F_{ss}$ (a valuation subring $R.\mathrm{integers}$ with surjective residue map whose kernel is its maximal ideal, compatible with $A$) satisfying $R.\mathrm{integers}\cap F_0=W_0$, $B\subseteq R.\mathrm{integers}$ and $F_{ss}$ generated as fractions of residues of elements of $B$, and for every place $Q$ of $F_{ss}$ over $\kappa(A)$ with the residues of $B$ lying in its valuation subring, there exist a subring $S$ of $\mathrm{fieldBar}\,q\,M'$ and ring homomorphisms $\varphi\colon A_b[X]\to S$, $\chi\colon S\to\kappa(A)$ such that: $S$ contains the image of $A_b$ and $\varphi$ sends constants to it; $\chi\circ\varphi$ sends $C\,a$ to the residue of $a$ in $\kappa(A)$ and $X$ to $0$; $S$ is local with $\ker\chi$ its maximal ideal; $S$ lies in $k_0(K_b)\sqcup F_0$ and has that compositum as fraction field; $\varphi$ is formally smooth, formally unramified and essentially of finite type; $S\subseteq R.\mathrm{integers}$ with $f\in S$ lying in $\mathfrak m_{R.\mathrm{integers}}$ exactly when $\varphi(C\,\varpi_b)\mid f$; for each $f\in S$ the $R$-residue of $f$ lies in the valuation subring of $Q$ and reduces there to the image of $\chi(f)$ in the residue field of $Q$; the $R$-residue of $\varphi(X)$ has $Q$-order $1$; and $B\subseteq S$, with $S$ consisting exactly of the quotients $g/h$, $g,h\in B$, whose denominator has nonzero residue at $Q$.
--
--   This describes the stalk of an affine chart of the model at a smooth $\kappa(A)$-rational point of the supersingular fibre: the chart $B$ is localised at the point determined by $Q$, and the resulting local ring is presented with an étale coordinate over $A_b[X]$ together with its residue character to $\kappa(A)$, in the shape required by the comparison of a regular prolongation with a formally étale henselian local model. It is invoked by the results that assemble the base smooth-point stalks for the full-level curve and their localisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_smoothPointStalk_of_affineChart.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.supersingularProlongation_smoothPointStalk_of_affineChart
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (s : ↥W)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)
    (halgc : IsAlgClosed (ResidueField ↥A))

    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKb : Kb = ⊥) (Ab : ValuationSubring ↥Kb) (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (hdvrb : IsDiscreteValuationRing ↥Ab) (hhensb : HenselianLocalRing ↥Ab)
    (ϖb : ↥Ab) (hϖb : maximalIdeal ↥Ab = Ideal.span {ϖb}) (hϖb0 : ϖb ≠ 0) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')) (W₀ : ValuationSubring ↥F₀),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      ∀ (B : Subring ↥(fieldBar q M')) (alg : Algebra ↥Ab ↥B),
        (∀ a : ↥Ab, ((@algebraMap ↥Ab ↥B _ _ alg a : ↥B) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) → (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
        (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥B, (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) →
        @Algebra.FormallySmooth ↥Ab ↥B _ _ alg → @Algebra.FinitePresentation ↥Ab ↥B _ _ alg →
        Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {@algebraMap ↥Ab ↥B _ _ alg ϖb}) →
        (∀ f : ↥(fieldBar q M'), f ∈ B → ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ W₀) → Prime (@algebraMap ↥Ab ↥B _ _ alg ϖb) →
        (∀ f : ↥F₀, f ∈ W₀ ↔ ∃ g h : ↥B, ¬ (@algebraMap ↥Ab ↥B _ _ alg ϖb ∣ h) ∧ (f : ↥(fieldBar q M')) * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) →
      ∀ (FSS : Type) [Field FSS] [Algebra (ResidueField ↥A) FSS] (R : RegularProlongation A ↥(fieldBar q M') FSS),
        (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ R.integers ↔ f ∈ W₀)) →
        ∀ (hBR : ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ R.integers)

          (hfracB : ∀ x : FSS, ∃ g h : ↥B, R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hBR _ (h).2⟩ ≠ 0 ∧ x * R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hBR _ (h).2⟩ = R.residue ⟨((g : ↥B) : ↥(fieldBar q M')), hBR _ (g).2⟩)
          (Q : Place (ResidueField ↥A) FSS) (hQ : ∀ b : ↥B, R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ (b).2⟩ ∈ Q.toValuationSubring),
        ∃ (S : Subring ↥(fieldBar q M')) (φ : Polynomial ↥Ab →+* ↥S) (χ : ↥S →+* ResidueField ↥A),

        (∀ a : ↥Ab, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ)) ∈ S) ∧
        (∀ a : ↥Ab, ((φ (Polynomial.C a) : ↥S) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) ∧
        (∀ a : ↥Ab, χ (φ (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩) ∧
        χ (φ Polynomial.X) = 0 ∧

        (∃ _ : IsLocalRing ↥S, RingHom.ker χ = maximalIdeal ↥S) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ S → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
        (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥S, (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

        (φ).FormallySmooth ∧ (φ).FormallyUnramified ∧ (φ).EssFiniteType ∧

        (∃ hSR : ∀ f : ↥S, (f : ↥(fieldBar q M')) ∈ R.integers,
          ∀ f : ↥S, (⟨(f : ↥(fieldBar q M')), hSR f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔ φ (Polynomial.C ϖb) ∣ f) ∧

        (∀ f : ↥S, ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
          IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
            algebraMap (ResidueField ↥A) Q.ResidueField (χ f)) ∧
        (∃ hR : ((φ Polynomial.X : ↥S) : ↥(fieldBar q M')) ∈ R.integers,
          Q.ord (R.residue ⟨((φ Polynomial.X : ↥S) : ↥(fieldBar q M')), hR⟩) = 1) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ S) ∧
        (∀ f : ↥(fieldBar q M'), f ∈ S ↔ ∃ g h : ↥B, (∃ hm : R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hBR _ (h).2⟩ ∈ Q.toValuationSubring,
            IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hBR _ (h).2⟩, hm⟩ ≠ 0) ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) := by sorry
