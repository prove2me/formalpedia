-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_map_jChartFin_not_mem_ssJSet_of_algEquiv_apply_qExpand_eq_twoChartIntegralModel
-- name    : ModularCurve.FullLevel.map_jChartFin_not_mem_ssJSet_of_algEquiv_apply_qExpand_eq_twoChartIntegralModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/297b7a34-3e92-5873-9681-e0bdf503e021
-- title:
--   Transport of non-supersingularity along σ fixing j(qτ)
-- statement:
--   Fix a prime $q$ with $5 \le q$, a nonzero natural number $M'$ with $q \nmid M'$, and a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime q`, i.e. $q$ lies in the non-units of $A$. Let $W$ be a finite set of places of `modularFunctionFieldC (ResidueField A) M'` over the residue field of $A$ — here `modularFunctionFieldC K N` is the intermediate field of $K((\mathsf q))$ generated over $K$ by the $j$-expansion `jqModC K` and its $N$-fold expansion `jqNModC K N` — and assume `hW`: a place $w$ lies in $W$ precisely when it lies in `ssPlaces q M' (ResidueField A)`, that is, when $w$ is rational (the structure map of the residue field of $w$ is surjective), satisfies `IsAffineGeomPlace`, and the value $w.\mathrm{evalAt}$ of `jGeomGen` at $w$ lies in the supersingular set `ssJSet q (ResidueField A)`; by definition `ssJSet p K` consists of those $j \in K$ such that every elliptic Weierstrass curve over $K$ with invariant $j$ has no nonzero point killed by $p$.
--
--   Assume `hle`: `modularFunctionFieldBar M'`, the field generated over $\overline{\mathbb{Q}}$ inside $\overline{\mathbb{Q}}((\mathsf q))$ by the coefficientwise images of the full level-$M'$ modular function field, is contained in `fieldBar q M'` $=$ `xHFunctionFieldBar (q^2 * M') (levelH q M')`, where `levelH q M'` is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, i.e. the units congruent to $1$ modulo $q$. Let $R_0$ be a `ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M')`: a valuation subring `R₀.integers` of the first field, a surjective residue homomorphism onto the second with kernel the maximal ideal, a map on places, and the remaining axioms of that structure (compatibility with $A$, existence of scalings with nonzero residue, preservation of degrees and of order functions). The hypothesis `hR₀` requires that for every Laurent series $y$ with coefficients in $A$ whose coefficientwise image in $\overline{\mathbb{Q}}((\mathsf q))$ lies in `modularFunctionFieldBar M'`, that element belongs to `R₀.integers` and its $R_0$-residue, read as a Laurent series over the residue field of $A$, is the coefficientwise reduction of $y$.
--
--   Let $\zeta$ be a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$ (an element of `Idx q`), and let $O_{\mathrm{Ig}}$ assign a valuation subring of `fieldBar q M'` to each point of the projective line $\mathbb{P}^1(\mathbb{Z}/q)$ and $O_{\mathrm{SS}}$ a valuation subring of `fieldBar q M'` to each element of $W$. The Igusa-component hypotheses are: `hIg_inf`, an element $f$ lies in $O_{\mathrm{Ig}}(\ell_\infty)$, $\ell_\infty = [1:0]$, if and only if there are Laurent series $x, y$ over $A$ with the coefficientwise reduction of $y$ nonzero and $f \cdot x_A = x'_A$ in the sense that $f$ times the coefficientwise image of $y$ equals that of $x$; `hIg`, for every $\ell$ there is $\gamma \in SL_2(\mathbb{Z})$ lying in $\Gamma_0(M')$ whose reduction `redQ q γ` carries $\ell_\infty$ to $\ell$ and for which $O_{\mathrm{Ig}}(\ell)$ is the pullback of $O_{\mathrm{Ig}}(\ell_\infty)$ along `levelAutBar q M' ζ γ`; `hIg_inj`, injectivity of $O_{\mathrm{Ig}}$; and `hIg_perm`, for every primitive $q$-th root of unity $\zeta'$ and every $\gamma \in \Gamma_0(M')$ there is a permutation $\sigma$ of $\mathbb{P}^1(\mathbb{Z}/q)$ with the pullback of $O_{\mathrm{Ig}}(\ell)$ along `levelAutBar q M' ζ' γ` equal to $O_{\mathrm{Ig}}(\sigma \ell)$ for all $\ell$.
--
--   The supersingular-chart hypotheses are: `hSS_A`, for each $s \in W$ and $x \in \overline{\mathbb{Q}}$ the image of $x$ lies in $O_{\mathrm{SS}}(s)$ if and only if $x \in A$; `hSS_over`, for each $s \in W$ and each $f \in R_0.\mathrm{integers}$ such that $f$ has non-negative order at every place of `modularFunctionFieldBar M'` over $\overline{\mathbb{Q}}$ at which the element `coeffEmb (AlgebraicClosure ℚ) jq` of that field has non-negative order, if the $R_0$-residue of $f$ lies in the valuation subring of the place $s$, then the image of $f$ in `fieldBar q M'` lies in $O_{\mathrm{SS}}(s)$, and for every $a \in A$ whose residue equals the value of the $R_0$-residue of $f$ at $s$, the difference of the image of $f$ and the image of $a$ lies in $O_{\mathrm{SS}}(s)$ and in its maximal ideal; `hSS_fix`, each $O_{\mathrm{SS}}(s)$ is its own pullback along `levelAutBar q M' ζ' γ` for all $\zeta'$ and all $\gamma \in \Gamma_0(M')$; and `hSS_tr`, for each $s \in W$ there is $t \in O_{\mathrm{SS}}(s)$ such that $t$ minus the image of any $a \in A$ is a unit of $O_{\mathrm{SS}}(s)$. Further, $R$ is a `RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))` with `hR`: $R.\mathrm{integers} = O_{\mathrm{Ig}}(\ell_\infty)$, and `hR₀O`: an element of `modularFunctionFieldBar M'` lies in $R_0.\mathrm{integers}$ exactly when its image in `fieldBar q M'` lies in $O_{\mathrm{Ig}}(\ell_\infty)$.
--
--   On the arithmetic side: $\pi \in \overline{\mathbb{Q}}$ with $\pi^{q^2-1} = q$ and $\pi \in A$; an intermediate field $k_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ and $\pi_0 \in k_0$ lying in $A$ such that $A \cap k_0$ (the pullback of $A$ to $k_0$) is a discrete valuation ring (`hdvr`) with maximal ideal generated by $\pi_0$ (`hunif`), is henselian local (`hhens`) and has algebraically closed residue field (`hres`), together with `hκ`: every $a \in A$ differs from some $c \in k_0 \cap A$ by an element of the maximal ideal of $A$. Moreover a prime $\ell$ with $3 \le \ell$, $\ell \ne q$, $\ell \nmid M'$; an element $\zeta_0 \in k_0$ which is a primitive $q\ell$-th root of unity in $\overline{\mathbb{Q}}$; and $\varpi_t \in k_0$ lying in $A$ with $\varpi_t^{q^2-1} = q u$ for some unit $u$ of $A$. Finally $K_1$ is a finite extension of $k_0$ inside $\overline{\mathbb{Q}}$ and $A_1$ a valuation subring of $K_1$ consisting exactly of the elements of $K_1$ lying in $A$, which is a discrete valuation ring and henselian local.
--
--   With `fieldBar q M'` made a $k_0$-algebra through $\overline{\mathbb{Q}}$, the assertion is the following. Let $F_0$ be an intermediate field of `fieldBar q M'` over $k_0$ such that: the join of the $k_0$-subfield generated by the image of $\overline{\mathbb{Q}}$ with $F_0$ is all of `fieldBar q M'`; $F_0$ is stable under every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$; for every finite extension $K'$ of $k_0$ in $\overline{\mathbb{Q}}$, every $m$, every family $c : \mathrm{Fin}\, m \to \overline{\mathbb{Q}}$ that is $K'$-linearly independent and every family $a$ of elements of the join of the $k_0$-subfield generated by the image of $K'$ with $F_0$, the relation $\sum_i c_i a_i = 0$ forces $a_i = 0$ for all $i$; and every element of `fieldBar q M'` whose underlying Laurent series lies in the range of `coeffEmb (AlgebraicClosure ℚ)` belongs to $F_0$. Write $E$ for the join of the $k_0$-subfield of `fieldBar q M'` generated by the image of $K_1$ with $F_0$, equipped with an $A_1$-algebra structure whose structure map is the inclusion, in the sense that the image in `fieldBar q M'` of $a \in A_1$ is the image of $a$ under $K_1 \subseteq \overline{\mathbb{Q}} \to$ `fieldBar q M'`. Let $j_1 \in E$ be the element whose image in `fieldBar q M'` is the inclusion of `coeffEmb (AlgebraicClosure ℚ) jq`, and assume $j_1 \ne 0$; write $\mathrm{chartAlgFin}$ for the subalgebra [`AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥E j₁`](def/AlgebraicCurve_TwoChartIntegralModel.html#L142) of elements of $E$ integral over $A_1[j_1]$, `jChartFin` for $j_1$ viewed in it, and `XFin` for the spectrum of this subalgebra. Let $j' \in E$ be an element whose Laurent series is `coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq)`, the $q$-fold expansion of the $j$-series, and assume $j'$ lies in $\mathrm{chartAlgFin}$. Let $\sigma$ be an $A_1$-algebra automorphism of $E$ with $\sigma j' = j'$ and such that $b \in \mathrm{chartAlgFin}$ if and only if $\sigma b \in \mathrm{chartAlgFin}$, and let $y, y'$ be points of `XFin` such that for every $b \in \mathrm{chartAlgFin}$ with $\sigma^{-1} b \in \mathrm{chartAlgFin}$ one has $b \in y'.\mathrm{asIdeal}$ if and only if $\sigma^{-1} b \in y.\mathrm{asIdeal}$.
--
--   Under these assumptions, if for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from $\mathrm{chartAlgFin}$ to $\Omega$ with kernel $y.\mathrm{asIdeal}$ the value $\varphi(\mathrm{jChartFin})$ does not lie in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), then for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi'$ from $\mathrm{chartAlgFin}$ to $\Omega$ with kernel $y'.\mathrm{asIdeal}$ the value $\varphi'(\mathrm{jChartFin})$ does not lie in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7).
--
--   The statement transports the condition ‘the specialisation of $j$ is not a supersingular invariant’ from a point $y$ of the $j$-finite chart of the two-chart integral model to its image $y' = \sigma(y)$ under an $A_1$-algebra automorphism fixing the $q$-expansion $j(q\tau)$; the mechanism is Kronecker's congruence $\Phi_q(X,Y) \equiv (X^q - Y)(X - Y^q) \bmod q$ for the modular equation of level $q$, in the form of [`ModularCurve.sub_mul_sub_mem_span_natCast_of_jqModC_mem_of_jqNModC_mem`](thm.html#ModularCurve.sub_mul_sub_mem_span_natCast_of_jqModC_mem_of_jqNModC_mem), together with the stability of the supersingular set under $q$-th powers ([`ModularCurve.pow_mem_ssJSet_iff`](thm.html#ModularCurve.pow_mem_ssJSet_iff)). It is used by [`ModularCurve.FullLevel.exists_levelAutBar_smul_centred_twoChartIntegralModel_of_forall_not_ssTube`](thm.html#ModularCurve.FullLevel.exists_levelAutBar_smul_centred_twoChartIntegralModel_of_forall_not_ssTube) in the construction of the semistable model of the modular curve at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_map_jChartFin_not_mem_ssJSet_of_algEquiv_apply_qExpand_eq_twoChartIntegralModel.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.map_jChartFin_not_mem_ssJSet_of_algEquiv_apply_qExpand_eq_twoChartIntegralModel
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

    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →

    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],

    ∀ (j' : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) →
      j' ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ →
    ∀ (σ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) ≃ₐ[↥A₁] ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      σ j' = j' →
      (∀ b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ ↔ σ b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →

    ∀ (y y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)),
      (∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)) (hb : σ.symm (b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁),
          b ∈ y'.asIdeal ↔ (⟨σ.symm (b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)), hb⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)) ∈ y.asIdeal) →

      (∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω) →
      ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
        (φ' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ' = y'.asIdeal →
          φ' (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω := by sorry
