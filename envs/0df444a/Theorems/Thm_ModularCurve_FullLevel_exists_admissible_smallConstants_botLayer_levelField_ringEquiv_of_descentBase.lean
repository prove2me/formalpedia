-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_admissible_smallConstants_botLayer_levelField_ringEquiv_of_descentBase
-- name    : ModularCurve.FullLevel.exists_admissible_smallConstants_botLayer_levelField_ringEquiv_of_descentBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/8c328c00-55e2-5965-a867-7528732d2f02
-- title:
--   Bottom-layer admissibility and identification of the level field
-- statement:
--   Fix a prime $q$ with $q \ge 5$ and a natural number $M' \neq 0$ with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` lying over $q$ in the sense of `LiesOverPrime`, i.e. $q$ is a non-unit of $A$. Write $\overline{F}_{M'} =$ `modularFunctionFieldBar M'` for the $\overline{\mathbb Q}$-subfield of $\overline{\mathbb Q}((t))$ obtained by adjoining to $\overline{\mathbb Q}$ the images under coefficientwise extension of the full-level modular function field `modularFunctionFieldFull M'`, and $\overline{F} =$ `fieldBar q M'` for the analogous base change of the function field of the modular curve of level $q^2M'$ attached to the subgroup $H =$ `levelH q M'`, the kernel of the reduction $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$. The hypothesis `hle` asserts $\overline{F}_{M'} \le \overline{F}$.
--
--   The geometric data consist of: a finite set $W$ of places of `modularFunctionFieldC (ResidueField A) M'` over the residue field of $A$, which by `hW` is exactly the set `ssPlaces q M' (ResidueField A)` of supersingular places (those places which are rational, are affine geometric places, and whose value at the geometric $j$-generator lies in the supersingular set `ssJSet q`); a constant-reduction datum $R_0$ of type `ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M')`, that is, a valuation subring `R₀.integers` of $\overline{F}_{M'}$, a surjective residue homomorphism onto `modularFunctionFieldC (ResidueField A) M'` with kernel the maximal ideal, a map on places preserving degrees, and the compatibility axioms of that structure; and the hypothesis `hR₀`, which says that for every Laurent series $y$ with coefficients in $A$ whose image in $\overline{\mathbb Q}((t))$ lies in $\overline{F}_{M'}$, that image lies in `R₀.integers` and its $R_0$-residue is, as a Laurent series over the residue field of $A$, the coefficientwise reduction of $y$. Further, an element $\pi \in A$ with $\pi^{q^2-1} = q$, and an element $\zeta$ of `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb Q}$; for $\gamma \in \mathrm{SL}_2(\mathbb Z)$ the automorphism `levelAutBar q M' ζ' γ` is the $\overline{\mathbb Q}$-algebra automorphism of $\overline{F}$ singled out by the predicate `IsLevelAutBar` (with value the identity if none exists).
--
--   Two families of valuation subrings of $\overline{F}$ are given: $\mathcal O_{\mathrm{Ig}} =$ `OIg`, indexed by [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21) $= \mathbb P^1(\mathbb Z/q)$, and $\mathcal O_{\mathrm{ss}} =$ `OSS`, indexed by $W$. The Igusa hypotheses are: `hIg_inf`, that $\mathcal O_{\mathrm{Ig}}$ at the point `lineInfty q` $= [1:0]$ consists exactly of those $f$ whose Laurent expansion can be written as a quotient $x/y$ with $x,y$ Laurent series over $A$ and the coefficientwise reduction of $y$ non-zero; `hIg`, that every $\ell \in \mathbb P^1(\mathbb Z/q)$ is of the form $\mathrm{red}_q(\gamma)\cdot[1:0]$ for some $\gamma \in \Gamma_0(M')$ with $\mathcal O_{\mathrm{Ig}}(\ell)$ the pullback of $\mathcal O_{\mathrm{Ig}}([1:0])$ along `levelAutBar q M' ζ γ`; `hIg_inj`, that $\mathcal O_{\mathrm{Ig}}$ is injective; and `hIg_perm`, that for every primitive $q$-th root of unity $\zeta'$ and every $\gamma \in \Gamma_0(M')$ the pullbacks along `levelAutBar q M' ζ' γ` permute the family $\mathcal O_{\mathrm{Ig}}$.
--
--   The supersingular hypotheses are: `hSS_A`, that for each $s \in W$ a constant from $\overline{\mathbb Q}$ lies in $\mathcal O_{\mathrm{ss}}(s)$ precisely when it lies in $A$; `hSS_over`, that for $s \in W$ and $f \in$ `R₀.integers` which is regular at every place of $\overline{F}_{M'}$ over $\overline{\mathbb Q}$ at which the image of $\hat\jmath =$ `coeffEmb _ jq` is regular, if the $R_0$-residue of $f$ lies in the valuation subring of the place $s$, then the image of $f$ in $\overline{F}$ lies in $\mathcal O_{\mathrm{ss}}(s)$ and, for every $a \in A$ whose residue equals the value of $s$ at that $R_0$-residue, the difference of the image of $f$ and $a$ lies in the maximal ideal of $\mathcal O_{\mathrm{ss}}(s)$; `hSS_fix`, that each $\mathcal O_{\mathrm{ss}}(s)$ is its own pullback along every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$; and `hSS_tr`, that each $\mathcal O_{\mathrm{ss}}(s)$ contains an element $t$ such that $t - a$ is a unit of $\mathcal O_{\mathrm{ss}}(s)$ for every $a \in A$.
--
--   The descent base consists of a subfield $K_0 \subseteq \overline{\mathbb Q}$ with $\overline{\mathbb Q}$ algebraic over $K_0$ and $\pi \in K_0$; a henselian local discrete valuation domain $A_0$ with an injective local ring homomorphism $\iota : A_0 \to A$ whose image in $\overline{\mathbb Q}$ is exactly $A \cap K_0$ (`hιK₀`), such that the composite of $\iota$ with the residue map of $A$ is surjective (`hres`); a generator $\varpi_0$ of the maximal ideal of $A_0$ (`hϖ₀`) with $\iota(\varpi_0) = \pi$ in $\overline{\mathbb Q}$ (`hϖ₀π`). Finally, a subfield $F_0 \subseteq \overline{F}$ characterised by `hF₀` as the set of those $f$ all of whose Laurent coefficients lie in $K_0$, with `hjF₀` asserting that the image of $\hat\jmath$ in $\overline{F}$ lies in $F_0$, together with an $A_0$-algebra structure on $F_0$ for which, by `hj₀`, the structure map sends $a$ to the image of $\iota(a)$ under $\overline{\mathbb Q} \to \overline{F}$.
--
--   The conclusion asserts the existence of an intermediate field $k_0$ of $\overline{\mathbb Q}/\mathbb Q$ and an element $\pi_0 \in k_0$ whose image lies in $A$, such that: the underlying set of $k_0$ equals that of $K_0$; $\pi_0 = \pi$ in $\overline{\mathbb Q}$; the ring $A \cap k_0$, formed as the pullback `A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))`, is a discrete valuation ring whose maximal ideal is generated by $\pi_0$, is henselian local, and has algebraically closed residue field; every $a \in A$ admits $c \in k_0$ with $c \in A$ and $a - c$ in the maximal ideal of $A$; there exists a prime $\ell$ with $3 \le \ell$, $\ell \neq q$, $\ell \nmid M'$, and an element $\zeta_0 \in k_0$ which is a primitive $(q\ell)$-th root of unity; there exists a unit $u$ of $A$ with $\pi_0^{q^2-1} = q\,u$; and there exists a ring isomorphism $e : A_0 \cong A \cap k_0$ compatible with $\iota$, in the sense that the image of $e(a)$ in $\overline{\mathbb Q}$ is $\iota(a)$ for all $a \in A_0$.
--
--   In addition, the conclusion contains the bottom-layer clauses for the trivial intermediate field $\bot$ of $\overline{\mathbb Q}/k_0$: an element of $\bot$ lies in `A.comap (algebraMap ↥⊥ (AlgebraicClosure ℚ))` if and only if its image lies in $A$; $\bot$ is finite-dimensional over $k_0$; that pullback ring is a discrete valuation ring and is henselian local; and there exists a ring isomorphism $e_0 : A_0 \cong$ that ring such that the image of $e_0(a)$ in $\overline{\mathbb Q}$ is $\iota(a)$ for all $a \in A_0$.
--
--   Finally, with $\overline{F}$ regarded as a $k_0$-algebra through $k_0 \to \overline{\mathbb Q} \to \overline{F}$, the conclusion provides an intermediate field $F_0'$ of $\overline{F}/k_0$ such that: $f \in F_0'$ if and only if every Laurent coefficient of $f$ is the image of an element of $k_0$; the join of $F_0'$ with the $k_0$-subfield generated by the range of $\overline{\mathbb Q} \to \overline{F}$ is all of $\overline{F}$; $F_0'$ is stable under `levelAutBar q M' ζ' γ` for every primitive $q$-th root of unity $\zeta'$ and every $\gamma \in \Gamma_0(M')$; for every finite extension $K'$ of $k_0$ inside $\overline{\mathbb Q}$, every $m$, every $c : \mathrm{Fin}\,m \to \overline{\mathbb Q}$ and every $a : \mathrm{Fin}\,m \to \overline{F}$ with all $a_i$ in the join of $F_0'$ with the $k_0$-subfield generated by the image of $K'$, linear independence of $c$ over $K'$ and $\sum_i c_i a_i = 0$ force $a_i = 0$ for all $i$; every $f \in \overline{F}$ whose Laurent series lies in the range of `coeffEmb (AlgebraicClosure ℚ)`, that is, has all coefficients rational, belongs to $F_0'$; $F_0'$ and $F_0$ have the same elements; and there is a ring isomorphism $\Phi$ from $F_0$ onto the join of $F_0'$ with the $k_0$-subfield of $\overline{F}$ generated by the image of $\bot$, which preserves underlying elements of $\overline{F}$.
--
--   This is the bottom-layer instance of the admissible descent data for the two-chart Igusa–Drinfeld model of the full-level modular curve: it upgrades the admissibility package of [`ModularCurve.FullLevel.exists_admissible_smallConstants_of_descentBase`](thm.html#ModularCurve.FullLevel.exists_admissible_smallConstants_of_descentBase) by the clauses for the trivial layer $\bot$ over $k_0$ and by an identification of the level field produced by [`ModularCurve.FullLevel.exists_levelField_coeff_mem_sup_eq_top_levelAutBar_stable_linearDisjoint`](thm.html#ModularCurve.FullLevel.exists_levelField_coeff_mem_sup_eq_top_levelAutBar_stable_linearDisjoint) with the coefficient field $F_0$. It is the shared first step of the component, uniqueness and dichotomy arguments for the Igusa charts, and is invoked by the descent statements about the Igusa and Drinfeld rings at finite layers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_admissible_smallConstants_botLayer_levelField_ringEquiv_of_descentBase.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve IsLocalRing CongruenceSubgroup
open ModularCurve.FullLevel
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_admissible_smallConstants_botLayer_levelField_ringEquiv_of_descentBase
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
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
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

    (K₀ : Subfield (AlgebraicClosure ℚ)) [Algebra.IsAlgebraic ↥K₀ (AlgebraicClosure ℚ)] (hπK₀ : π ∈ K₀)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hιK₀ : Set.range (fun a : A₀ => ((ι a : ↥A) : AlgebraicClosure ℚ)) =
      (A : Set (AlgebraicClosure ℚ)) ∩ (K₀ : Set (AlgebraicClosure ℚ)))
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})

    (hϖ₀π : ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) = π)

    (F₀ : Subfield ↥(fieldBar q M'))
    (hF₀ : ∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K₀)

    (hjF₀ : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)

    [Algebra A₀ ↥F₀]
    (hj₀ : ∀ a : A₀, ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ)) :
    ∃ (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ₀ : (π₀ : AlgebraicClosure ℚ) ∈ A),
      (k₀ : Set (AlgebraicClosure ℚ)) = (K₀ : Set (AlgebraicClosure ℚ)) ∧ (π₀ : AlgebraicClosure ℚ) = π ∧

      IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ∧
      maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) = Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))} ∧
      HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ∧
      IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧
      (∀ a : AlgebraicClosure ℚ, a ∈ A → ∃ c : ↥k₀, (c : AlgebraicClosure ℚ) ∈ A ∧
        ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A) ∧

      (∃ ℓ : ℕ, ℓ.Prime ∧ 3 ≤ ℓ ∧ ℓ ≠ q ∧ ¬ ℓ ∣ M' ∧
        ∃ ζ₀ : ↥k₀, IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ)) ∧
      (∃ u : ↥A, IsUnit u ∧ (π₀ : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ)) ∧

      (∃ e : A₀ ≃+* ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ∀ a : A₀,
        algebraMap ↥k₀ (AlgebraicClosure ℚ) ((e a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀) = ((ι a : ↥A) : AlgebraicClosure ℚ)) ∧

      (∀ x : ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), x ∈ (A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↔ (x : AlgebraicClosure ℚ) ∈ A) ∧
      FiniteDimensional ↥k₀ ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ∧
      IsDiscreteValuationRing ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ∧
      HenselianLocalRing ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ∧
      (∃ e₀ : A₀ ≃+* ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))),
        ∀ a : A₀, (((e₀ a : ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)))) : ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))) : AlgebraicClosure ℚ) = ((ι a : ↥A) : AlgebraicClosure ℚ)) ∧

      (letI : Algebra ↥k₀ ↥(fieldBar q M') :=
        ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
       ∃ F₀' : IntermediateField ↥k₀ ↥(fieldBar q M'),
        (∀ f : ↥(fieldBar q M'), f ∈ F₀' ↔ ∀ n : ℤ, ∃ c : ↥k₀, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n = ((c : ↥k₀) : AlgebraicClosure ℚ)) ∧
        (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀' = ⊤) ∧
        (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀' → levelAutBar q M' ζ' γ f ∈ F₀') ∧
        (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
          ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀') →
            LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) ∧
        (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀') ∧
        (∀ f : ↥(fieldBar q M'), f ∈ F₀' ↔ f ∈ F₀) ∧
        ∃ Φ : ↥F₀ ≃+* ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀'),
          ∀ f : ↥F₀, ((Φ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) : ↥(fieldBar q M')) = (f : ↥(fieldBar q M'))) := by sorry
