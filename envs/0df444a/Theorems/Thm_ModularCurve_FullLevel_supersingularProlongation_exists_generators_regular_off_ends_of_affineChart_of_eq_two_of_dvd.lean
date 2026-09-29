-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_exists_generators_regular_off_ends_of_affineChart_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.supersingularProlongation_exists_generators_regular_off_ends_of_affineChart_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/642061c3-579f-5fff-8846-c129e1b8c0a4
-- title:
--   Generators regular off the ends from an affine chart, q=2
-- statement:
--   Fix the prime $q$ together with the hypothesis `hq2` that $q=2$, a non-zero level $M'$ with `hqM'` asserting $q \nmid M'$, and an auxiliary prime $\ell$ subject to `hℓ12` ($\ell \equiv 11 \bmod 12$) and `hℓM'` ($\ell \mid M'$). Let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` with `hA` asserting `A.LiesOverPrime q`, i.e. $q$ lies in the non-units of $A$; write $\kappa =$ `ResidueField A`. Let $W$ be a finite set of places of `modularFunctionFieldC κ M'` over $\kappa$, and `hW` the hypothesis that $W$ is exactly `ssPlaces q M' κ`, the set of places $w$ that are rational, are affine geometric places, and have $w(\,$`jGeomGen`$\,)$ in the supersingular $j$-set `ssJSet q κ`; let $s \in W$.
--
--   The hypothesis `hle` states the inclusion `modularFunctionFieldBar M' ≤ fieldBar q M'` of intermediate fields of `LaurentSeries` $\overline{\mathbb Q}$, where the first is the base change to $\overline{\mathbb Q}$ of the full modular function field of level $M'$ and the second is the base change `xHFunctionFieldBar (q^2*M') (levelH q M')`. Further data: a `ConstantReduction` $R_0$ of `modularFunctionFieldBar M'` with residue field `modularFunctionFieldC κ M'` over $A$ — that is, a valuation subring $R_0$.`integers` compatible with $A$ together with a surjective residue homomorphism onto `modularFunctionFieldC κ M'` whose kernel is the maximal ideal, a place map preserving degrees, and the usual normalisation and order-transport clauses — and the hypothesis `hR₀`, which says that for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb Q}$ lies in `modularFunctionFieldBar M'`, that image lies in $R_0$.`integers` and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$.
--
--   On the supersingular side: a field `FSS`, an algebra over $\kappa$; a `RegularProlongation` $R$ of `fieldBar q M'` over $A$ with residue field `FSS` (a valuation subring $R$.`integers` compatible with $A$, with surjective residue map onto `FSS` of kernel the maximal ideal, and the scaling clause `exists_smul_mem`); a finite set $N$ of places of `FSS` over $\kappa$ (the ends); and, indexed by the places $Q$ of `FSS` over $\kappa$, a subring `Sx Q` of `fieldBar q M'`, a ring homomorphism `φx Q` from `Polynomial A` to `Sx Q`, a homomorphism `χ₀x Q` from `Sx Q` to $\kappa$, and a set `Dx Q` of places of `fieldBar q M'` over $\overline{\mathbb Q}$.
--
--   The hypotheses on these data are: `h0`, that `FSS` contains an element transcendental over $\kappa$; `h1`, that for $f$ in $R_0$.`integers` which is regular wherever the image of `jq` in `modularFunctionFieldBar M'` is regular (non-negative order at every place at which that image has non-negative order) and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in `fieldBar q M'` lies in $R$.`integers` and its $R$-residue is the image under $\kappa \to$ `FSS` of the value at $s$ of that $R_0$-residue; `h2`, that $R$.`integers` is stable under `levelAutBar q M' ζ γ` for every $\zeta$ in `Idx q` (the primitive $q$-th roots of unity in $\overline{\mathbb Q}$) and every $\gamma \in \Gamma_0(M')$; and `hcard`, that $N$ has exactly $q+1$ elements.
--
--   The hypothesis `hpkg` (thirteen clauses, summarised here) requires, for each place $Q \notin N$, that `(Sx Q, φx Q, χ₀x Q, Dx Q)` be a smooth-point package: $A$ maps into `Sx Q`; `φx Q` is formally smooth and formally unramified; `φx Q` composed with `Polynomial.C` is the structure map of $A$, and `χ₀x Q` recovers reduction on $A$ while killing `φx Q Polynomial.X`; for each $c \in A$ of residue $0$ there is a unique homomorphism `Sx Q → A` fixing $A$, reducing to `χ₀x Q`, and sending `φx Q Polynomial.X` to $c$; every element of `Sx Q` lies in $R$.`integers`, has $R$-residue in the valuation subring of $Q$, and there reduces to the image of its `χ₀x Q`-value; the $R$-residue of `φx Q Polynomial.X` has $Q$-order $1$; `Dx Q` consists exactly of the rational places $P$ of `fieldBar q M'` at which every element of `Sx Q` is integral with value in $A$, the value having $A$-valuation $<1$ precisely when `χ₀x Q` kills the element; each $A$-valued character of `Sx Q` over $A$ reducing to `χ₀x Q` is realised by a unique $P \in$ `Dx Q`; for $P \in$ `Dx Q` the valuation subring of $P$ is the set of fractions $g/h$ with $g,h \in$ `Sx Q` and $h$ not vanishing at $P$; any non-zero element of order $0$ at all $P \in$ `Dx Q` becomes a unit of `Sx Q` after multiplication by a non-zero constant; and any element of $R$.`integers` integral at all $P \in$ `Dx Q` lies in `Sx Q`.
--
--   Three further structural hypotheses: `hdisj`, that the discs `Dx Q` for distinct places $Q, Q' \notin N$ are disjoint; `hcusp`, that the image in `fieldBar q M'` of `jq` has non-negative order at every $P \in$ `Dx Q` for $Q \notin N$; and `heqv`, that for every $\tau$ in the subgroup generated by the automorphisms `levelAutBar q M' ζ γ` with $\zeta$ in `Idx q` and $\gamma \in \Gamma_0(M')$ which preserves $R$.`integers`, the induced residue automorphism `R.resAut τ` preserves $N$ setwise and carries discs to discs, `RegularProlongation.smulDisc τ (Dx Q) = Dx (R.resAut τ • Q)` for $Q \notin N$.
--
--   The hypothesis `hUniq` asserts uniqueness of these packages: for $Q \notin N$, any quadruple $(S, \varphi, \chi_0, D)$ satisfying the same thirteen clauses has $D =$ `Dx Q` and $S =$ `Sx Q` as sets, and $\chi_0$ agrees with `χ₀x Q` on common elements.
--
--   The hypothesis `hdl` is the Drinfeld identification: for any algebra structure of `GaloisField q 2` on $\kappa$ making [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) a domain, and for every $\zeta$ in `Idx q`, there exist a subgroup `Cs` of the group of $(q+1)$-st roots of unity in `GaloisField q 2` and a $\kappa$-algebra isomorphism $e$ from `FSS` onto the fixed field [`DrinfeldCurve.quotField q κ Cs`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) such that `Nat.card Cs` equals `placeWidthChar q M' s` (for $q = 2$ the quantity `jWidthChar`, equal to $12$ at $j = 0$ and $1$ otherwise, divided by `placeRamificationJ M' s`), and such that, for $\gamma \in \Gamma_0(M')$ with `levelAutBar q M' ζ γ⁻¹` preserving $R$.`integers` and with the pair `(redQ q γ, 1)` in [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276), the isomorphism $e$ intertwines the residue automorphism `R.resAut (levelAutBar q M' ζ γ⁻¹)` with the action [`DrinfeldCurve.hFunctionFieldAction q κ`](def/DrinfeldCurve_FunctionField.html#L16) of that pair on the Drinfeld function field.
--
--   The final hypothesis `haff` is the affine chart: there exists a subring $B$ of `fieldBar q M'` containing the image of $A$, contained in $R$.`integers`, contained in `Sx Q` for every $Q \notin N$, and such that every $z \in$ `FSS` lying in the valuation subring of every place $Q \notin N$ is the $R$-residue of some element of $B$.
--
--   Under these hypotheses the conclusion asserts the existence of a natural number $n$, elements $g_0, \dots, g_{n-1}$ of `fieldBar q M'` and proofs that each $g_i$ lies in $R$.`integers`, such that: first, for every index $i$, every place $Q \notin N$ and every $P \in$ `Dx Q`, the element $g_i$ lies in the valuation subring of $P$ and its value `P.evalAt (g i)` lies in $A$; and second, every $f \in$ `FSS` lying in the valuation subring of every place $Q \notin N$ belongs to the $\kappa$-subalgebra of `FSS` generated by the residues `R.residue ⟨g i, hg i⟩`.
--
--   This is the $q = 2$ case, at a level rigidified by an auxiliary prime $\ell \equiv 11 \bmod 12$ dividing $M'$, of the finite generation statement for the ring of functions on the supersingular component regular away from its ends: the functions of `FSS` regular off the $q+1$ ends are generated over the residue field by reductions of finitely many elements of `fieldBar q M'` that are integral with $A$-integral values on all smooth residue discs. It is the version in which an affine chart $B$ for the component is assumed, and it feeds the construction of generators compatible with the level orbits and the inertia action under the Drinfeld identification.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularProlongation_exists_generators_regular_off_ends_of_affineChart_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.supersingularProlongation_exists_generators_regular_off_ends_of_affineChart_of_eq_two_of_dvd
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
            Nat.card Cs = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
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
