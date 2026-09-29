-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_igusaBaseModel_smoothPointStalks
-- name    : ModularCurve.FullLevel.exists_igusaBaseModel_smoothPointStalks
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/fab105bc-3289-53b2-905e-d91941d7095b
-- title:
--   Smooth-point stalks of the Igusa base model at level q²M'
-- statement:
--   Throughout, $q$ is a prime with $5 \le q$ and $M'$ a non-zero natural number with $q \nmid M'$; $A$ is a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$ (the predicate `A.LiesOverPrime q` asserts $(q : \overline{\mathbb Q}) \in A.\mathrm{nonunits}$), and $\kappa :=$ `ResidueField A`. Write $H :=$ `levelH q M'`, the kernel of the reduction $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$, i.e. the units congruent to $1$ modulo $q$; let $F :=$ `fieldBar q M'` be the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the $q$-expansions of the modular functions of level $\Gamma_H(q^2M')$ defined over $\mathbb Q$, and $F_\kappa :=$ `xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')` the field obtained by the same recipe over $\kappa$. Write $\mathcal M :=$ `modularFunctionFieldBar M'`, the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the $q$-expansions of the full level-$M'$ modular function field over $\mathbb Q$, and $\mathcal M_\kappa :=$ `modularFunctionFieldC (ResidueField A) M'` $= \kappa(j(q), j(q^{M'}))$. Places are taken in the sense of the project's `Place K F`: a valuation subring of $F$ containing the image of $K$, different from $F$, and a principal ideal ring; `ord`, `evalAt` and `IsRational` are the associated order function, the value in $K$ at a place (via the inverse of $K \to$ residue field, or $0$ if the element is not integral), and surjectivity of $K \to$ residue field.
--
--   The data of the statement are: a finite set $W$ of places of $\mathcal M_\kappa$ over $\kappa$ together with `hW`, which says that $W$ is exactly the set of supersingular places, i.e. of those $w$ that are rational, satisfy `IsAffineGeomPlace` and have $w.\mathrm{evalAt}$ of the $j$-generator `jGeomGen` in `ssJSet q`; the inclusion `hle : modularFunctionFieldBar M' ≤ fieldBar q M'`; a `ConstantReduction` $R_0$ of $A$ from $\mathcal M$ to $\mathcal M_\kappa$ (a valuation subring $R_0.\mathrm{integers}$ of $\mathcal M$ meeting the constants in $A$, a surjective residue map onto $\mathcal M_\kappa$ with kernel the maximal ideal and compatible with $A \to \kappa$ on constants, a normalisation property, and a map on places preserving degrees and compatible with divisors of functions of non-zero reduction), together with `hR₀`, which says that a Laurent series with coefficients in $A$ whose image in $\overline{\mathbb Q}((q))$ lies in $\mathcal M$ lies in $R_0.\mathrm{integers}$ and reduces to the coefficientwise reduction of that series along $A \to \kappa$; a primitive $q$-th root of unity $\zeta$ (an element of `Idx q`); and two families of valuation subrings of $F$, namely $O^{\mathrm{Ig}} : \mathbb P^1(\mathbb F_q) \to$ `ValuationSubring (fieldBar q M')` and $O^{\mathrm{ss}} : W \to$ `ValuationSubring (fieldBar q M')`.
--
--   The hypotheses on $O^{\mathrm{Ig}}$ are: `hIg_inf`, which describes $O^{\mathrm{Ig}}(\infty)$ (at the line `lineInfty q` spanned by $(1,0)$) as the Gauss ring, $f \in O^{\mathrm{Ig}}(\infty)$ if and only if $f \cdot y = x$ for Laurent series $x,y$ with coefficients in $A$ with $y$ of non-zero coefficientwise reduction; `hIg`, that every line $\ell$ is $\mathrm{redQ}(\gamma) \cdot \infty$ for some $\gamma \in \Gamma_0(M')$ with $O^{\mathrm{Ig}}(\ell)$ the pull-back of $O^{\mathrm{Ig}}(\infty)$ along `levelAutBar q M' ζ γ`; `hIg_inj`, injectivity of $O^{\mathrm{Ig}}$; and `hIg_perm`, that for every $\zeta'$ and every $\gamma \in \Gamma_0(M')$ pulling back along `levelAutBar q M' ζ' γ` permutes the family $O^{\mathrm{Ig}}$. The hypotheses on $O^{\mathrm{ss}}$ are: `hSS_A`, that a constant $x \in \overline{\mathbb Q}$ lies in $O^{\mathrm{ss}}(s)$ if and only if $x \in A$; `hSS_over`, that for $s \in W$ and $f \in R_0.\mathrm{integers}$ whose order is non-negative at every place of $\mathcal M$ at which the $q$-expansion of $j$ has non-negative order, and whose reduction $R_0.\mathrm{residue}(f)$ is integral at $s$, the image of $f$ in $F$ lies in $O^{\mathrm{ss}}(s)$ and, for every $a \in A$ whose residue is the value at $s$ of $R_0.\mathrm{residue}(f)$, the difference of $f$ and $a$ lies in the maximal ideal of $O^{\mathrm{ss}}(s)$; `hSS_fix`, that $O^{\mathrm{ss}}(s)$ is invariant under pull-back along every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$; and `hSS_tr`, that each $O^{\mathrm{ss}}(s)$ contains an element $t$ such that $t - a$ is a unit of $O^{\mathrm{ss}}(s)$ for every $a \in A$. Further, $R$ is a `RegularProlongation` of $A$ from $F$ to $F_\kappa$ (the same axioms as a constant reduction, without the data on places) with $R.\mathrm{integers} = O^{\mathrm{Ig}}(\infty)$ (`hR`), and `hR₀O` asserts that an element of $\mathcal M$ lies in $R_0.\mathrm{integers}$ exactly when its image in $F$ lies in $O^{\mathrm{Ig}}(\infty)$.
--
--   The remaining data concern constants: an element $\pi \in A$ with $\pi^{q^2-1} = q$; an intermediate field $k_0$ of $\overline{\mathbb Q}/\mathbb Q$ and $\pi_0 \in k_0$ lying in $A$ such that $A \cap k_0$ (the pull-back of $A$ along $k_0 \to \overline{\mathbb Q}$) is a discrete valuation ring (`hdvr`) with maximal ideal generated by $\pi_0$ (`hunif`), is henselian local (`hhens`) and has algebraically closed residue field (`hres`), and `hκ`, that every $a \in A$ is congruent modulo the maximal ideal of $A$ to some element of $k_0$ lying in $A$; an auxiliary prime $\ell$ with $3 \le \ell$, $\ell \ne q$ and $\ell \nmid M'$, an element $\zeta_0 \in k_0$ which is a primitive $q\ell$-th root of unity, and an element $\varpi_t \in k_0$ lying in $A$ with $\varpi_t^{q^2-1} = q u$ for some unit $u$ of $A$; finally one finite layer of constants: an intermediate field $K_1$ of $\overline{\mathbb Q}/k_0$, finite-dimensional over $k_0$, and a valuation subring $A_1$ of $K_1$ with $A_1 = A \cap K_1$ (`hA₁`), assumed to be a discrete valuation ring and henselian local. The field $F$ is regarded as a $k_0$-algebra through $k_0 \subseteq \overline{\mathbb Q} \to F$.
--
--   The conclusion asserts the existence of an intermediate field $F_0$ of $F/k_0$, a finite set $N^{\mathrm{Ig}}$ of places of $F_\kappa$ over $\kappa$, and, for every place $Q$ of $F_\kappa$ over $\kappa$, a subring $S_Q \subseteq F$, a ring homomorphism $\varphi_Q : A_1[T] \to S_Q$, a ring homomorphism $\chi_Q : S_Q \to \kappa$ and a set $D_Q$ of places of $F$ over $\overline{\mathbb Q}$, subject to the following conjuncts.
--
--   First, the compositum of $F_0$ with the subfield generated over $k_0$ by the image of $\overline{\mathbb Q}$ is all of $F$. Second, $F_0$ is stable under every automorphism `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$. Third, $N^{\mathrm{Ig}}$ and $W$ have the same cardinality. Fourth, there is a ring homomorphism $j : \mathcal M_\kappa \to F_\kappa$ such that the reduction of the image in $F$ of any $f \in R_0.\mathrm{integers}$ lies in $R.\mathrm{integers}$ and equals $j(R_0.\mathrm{residue}(f))$, and such that $Q \in N^{\mathrm{Ig}}$ if and only if there is $s \in W$ with: an element $g \in \mathcal M_\kappa$ is integral at $s$ exactly when $j(g)$ is integral at $Q$. Fifth, every valuation subring of $F$ which contains all the constants $\overline{\mathbb Q}$ and is not the whole of $F$ is a principal ideal ring. Sixth, a linear disjointness statement: for every intermediate field $K'$ of $\overline{\mathbb Q}/k_0$ finite over $k_0$, every $m$, every $c : \mathrm{Fin}\,m \to \overline{\mathbb Q}$ linearly independent over $K'$, and every $a : \mathrm{Fin}\,m \to F$ with all $a_i$ in the compositum of $F_0$ with the subfield generated over $k_0$ by the image of $K'$, the vanishing of $\sum_i c_i a_i$ forces $a_i = 0$ for all $i$.
--
--   Seventh, for every place $Q$ of $F_\kappa$ with $Q \notin N^{\mathrm{Ig}}$: the map sending $a \in A_1$ to the residue of $a$ in $\kappa$ is surjective (a clause not depending on $Q$); every $a \in A_1$ has its image in $F$ inside $S_Q$; $\varphi_Q$ sends the constant $a$ to that image; $\chi_Q(\varphi_Q(a))$ is the residue of $a$ in $\kappa$; $\chi_Q(\varphi_Q(T)) = 0$; there is a local ring structure on $S_Q$ for which $\ker \chi_Q$ is the maximal ideal; $\varphi_Q$ is formally smooth, formally unramified and essentially of finite type; $S_Q$ is contained in the compositum of $F_0$ with the subfield generated over $k_0$ by the image of $K_1$, and conversely every element $f$ of that compositum can be written as a quotient, $f h = g$ with $g, h \in S_Q$ and $h \ne 0$; every element of $S_Q$ lies in $R.\mathrm{integers}$, and for every uniformiser $\varpi$ of $A_1$ and every $f \in S_Q$, the element $f$ lies in the maximal ideal of $R.\mathrm{integers}$ if and only if $\varphi_Q(\varpi)$ divides $f$ in $S_Q$; for every $f \in S_Q$ the reduction $R.\mathrm{residue}(f)$ is integral at $Q$ and its residue in the residue field of $Q$ is the image of $\chi_Q(f)$ under $\kappa \to Q.\mathrm{ResidueField}$; the reduction of $\varphi_Q(T)$ has order $1$ at $Q$; and $D_Q$ consists exactly of the places $P$ of $F$ over $\overline{\mathbb Q}$ which are rational, at which every $f \in S_Q$ is integral with value $P.\mathrm{evalAt}(f) \in A$, and for which, for every $f \in S_Q$, the value $P.\mathrm{evalAt}(f)$ has $A$-valuation less than $1$ if and only if $\chi_Q(f) = 0$.
--
--   Eighth, the discs are pairwise disjoint: for $Q, Q' \notin N^{\mathrm{Ig}}$, a place $P$ lying in $D_Q$ and in $D_{Q'}$ forces $Q = Q'$. Ninth, equivariance for the level automorphisms: for every $\tau$ in the subgroup of $\overline{\mathbb Q}$-automorphisms of $F$ generated by the `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$, and every proof that $\tau$ preserves $R.\mathrm{integers}$, the induced automorphism `R.resAut` of $F_\kappa$ over $\kappa$ satisfies: its action on a place $Q$ keeps $Q$ inside or outside $N^{\mathrm{Ig}}$, and for $Q \notin N^{\mathrm{Ig}}$ the transported disc `smulDisc τ (D Q)` $= \{P : \tau^{-1} \cdot P \in D_Q\}$ equals $D$ at the translated place. Tenth, invariance under inertia: for every $\tau$ in `A.inertiaSubgroupIn ℚ` mapping $K_1$ into itself and every $Q \notin N^{\mathrm{Ig}}$, the coefficientwise arithmetic Galois action of $\tau$ on $F$ preserves $S_Q$ in both directions, and $\chi_Q$ is unchanged by it. Eleventh, if $g$ lies in the same subgroup generated by the level automorphisms and pulls $O^{\mathrm{Ig}}(\infty)$ back to a different valuation subring, then for all $Q, Q' \notin N^{\mathrm{Ig}}$ and all $P \in D_Q$ one has $g \cdot P \notin D_{Q'}$. Twelfth, the discs avoid the supersingular tubes: for $Q \notin N^{\mathrm{Ig}}$, $P \in D_Q$ and $s \in W$, it is not the case that both of the following hold, namely that the image in $F$ of the $q$-expansion of $j$ is integral at $P$ and its value at $P$ is congruent modulo the maximal ideal of $A$ to every $a \in A$ whose residue is the value at $s$ of `jGeomGen`, and that the corresponding statement holds for the image of $j(q^{M'})$ (`qExpand ℚ M' jq`) and `jNGeomGen`. Thirteenth, conversely, every place $P$ of $F$ over $\overline{\mathbb Q}$ which, for each $s \in W$, fails the supersingular-tube condition (that for every $f \in R_0.\mathrm{integers}$ whose order is non-negative wherever the $q$-expansion of $j$ has non-negative order and whose reduction is integral at $s$, and every $a \in A$ whose residue is the value at $s$ of that reduction, the value $P.\mathrm{evalAt}(f)$ differs from $a$ by an element of the maximal ideal of $A$) is carried by some level automorphism into a disc: there are $\gamma \in \Gamma_0(M')$ and $Q \notin N^{\mathrm{Ig}}$ with `levelAutBar q M' ζ γ` $\cdot P \in D_Q$. Fourteenth, there is a place $P$ of $F$ whose valuation subring is `qIntegersBar`, the subring of elements of non-negative order in the Laurent variable, together with a $Q \notin N^{\mathrm{Ig}}$ such that $P \in D_Q$.
--
--   This is the stalk-level construction of a smooth integral model of the modular curve of level $\Gamma_H(q^2M')$, with $H$ the units congruent to $1$ modulo $q$, away from the supersingular locus: at one finite layer $K_1$ of constants it produces the Igusa components' complement as a family of formally étale local charts $A_1[T] \to S_Q$ over the non-supersingular places $Q$ of the special fibre, together with their residue discs $D_Q$ and the equivariance of the whole picture under the level automorphisms and under inertia. It is used by [`ModularCurve.FullLevel.exists_igusaTower_smoothPointData_of_stable`](thm.html#ModularCurve.FullLevel.exists_igusaTower_smoothPointData_of_stable), which propagates the data up the tower of constant fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_igusaBaseModel_smoothPointStalks.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.exists_igusaBaseModel_smoothPointStalks
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
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))

    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ₀ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [IsDiscreteValuationRing ↥A₁] [HenselianLocalRing ↥A₁] :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∃ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M'))
      (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))))
      (S : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Subring ↥(fieldBar q M'))
      (φ : (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) → (Polynomial ↥A₁ →+* ↥(S Q)))
      (χ : (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) → (↥(S Q) →+* ResidueField ↥A))
      (D : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),

      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) ∧
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) ∧

      NIg.card = W.card ∧

      (∃ j : modularFunctionFieldC (ResidueField A) M' →+* xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'),
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers, R.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
        ∀ Q, Q ∈ NIg ↔ ∃ s : ↥W, ∀ g : modularFunctionFieldC (ResidueField A) M',
          g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
            j g ∈ Q.toValuationSubring) ∧

      (∀ O : ValuationSubring ↥(fieldBar q M'), (∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') x ∈ O) → O ≠ ⊤ → IsPrincipalIdealRing ↥O) ∧

      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) ∧

      (∀ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg →

        Function.Surjective (fun a : ↥A₁ => IsLocalRing.residue ↥A ⟨((a : ↥K₁) : AlgebraicClosure ℚ), (hA₁ a).mp a.2⟩) ∧

        (∀ a : ↥A₁, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ) ∈ S Q) ∧
        (∀ a : ↥A₁, ((φ Q (Polynomial.C a) : ↥(S Q)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) ∧
        (∀ a : ↥A₁, χ Q (φ Q (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥K₁) : AlgebraicClosure ℚ), (hA₁ a).mp a.2⟩) ∧
        χ Q (φ Q Polynomial.X) = 0 ∧

        (∃ _ : IsLocalRing ↥(S Q), RingHom.ker (χ Q) = IsLocalRing.maximalIdeal ↥(S Q)) ∧

        (φ Q).FormallySmooth ∧ (φ Q).FormallyUnramified ∧ (φ Q).EssFiniteType ∧

        (∀ f : ↥(fieldBar q M'), f ∈ S Q → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
        (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥(S Q), (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

        (∃ hSR : ∀ f : ↥(S Q), (f : ↥(fieldBar q M')) ∈ R.integers,
          ∀ (ϖ : ↥A₁), IsLocalRing.maximalIdeal ↥A₁ = Ideal.span {ϖ} →
            ∀ f : ↥(S Q), (⟨(f : ↥(fieldBar q M')), hSR f⟩ : ↥R.integers) ∈ IsLocalRing.maximalIdeal ↥R.integers ↔ φ Q (Polynomial.C ϖ) ∣ f) ∧

        (∀ f : ↥(S Q), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
          IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
            algebraMap (ResidueField ↥A) Q.ResidueField (χ Q f)) ∧

        (∃ hR : ((φ Q Polynomial.X : ↥(S Q)) : ↥(fieldBar q M')) ∈ R.integers,
          Q.ord (R.residue ⟨((φ Q Polynomial.X : ↥(S Q)) : ↥(fieldBar q M')), hR⟩) = 1) ∧

        (∀ P, P ∈ D Q ↔ (P.IsRational ∧
          (∀ f : ↥(S Q), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
          (∀ f : ↥(S Q), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χ Q f = 0)))) ∧

          (∀ Q Q' : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg → Q' ∉ NIg → ∀ (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), P ∈ D Q → P ∈ D Q' → Q = Q') ∧

          (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
              ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))),
              (R.resAut τ hτ • Q ∈ NIg ↔ Q ∈ NIg) ∧
              (Q ∉ NIg → AlgebraicCurve.RegularProlongation.smulDisc τ (D Q) = D (R.resAut τ hτ • Q))) ∧

          (∀ τ ∈ A.inertiaSubgroupIn ℚ, (∀ x : AlgebraicClosure ℚ, x ∈ K₁ → τ x ∈ K₁) →
            ∀ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg →
              (∀ f : ↥(fieldBar q M'), f ∈ S Q ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • f ∈ S Q) ∧
              (∀ (f : ↥(S Q)) (hf : ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : ↥(fieldBar q M')) ∈ S Q),
                χ Q ⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : ↥(fieldBar q M')), hf⟩ = χ Q f)) ∧

          (∀ g ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
              ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            (OIg (lineInfty q)).comap g.toAlgHom.toRingHom ≠ OIg (lineInfty q) →
              ∀ Q Q' : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg → Q' ∉ NIg → ∀ (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), P ∈ D Q → g • P ∉ D Q') ∧

          (∀ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg → ∀ P ∈ D Q, ∀ s : ↥W, ¬ (((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ P.toValuationSubring ∧
              (∀ a : A, residue A a = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jGeomGen (ResidueField A) M') →
                ∃ h : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                  (⟨_, h⟩ : A) ∈ maximalIdeal A)) ∧
            ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ P.toValuationSubring ∧
              (∀ a : A, residue A a = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jNGeomGen (ResidueField A) M') →
                ∃ h : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                  (⟨_, h⟩ : A) ∈ maximalIdeal A)))) ∧

          (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'),
            (∀ s : ↥W, ¬ (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
                (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                  0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
                (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                  ∀ a : A, residue A a =
                      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                    ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                      (⟨_, h⟩ : A) ∈ maximalIdeal A)) →
            ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ ∃ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg ∧ levelAutBar q M' ζ γ • P ∈ D Q) ∧

          (∃ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P.toValuationSubring = qIntegersBar (AlgebraicClosure ℚ) (fieldBar q M') ∧
            ∃ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg ∧ P ∈ D Q) := by sorry
