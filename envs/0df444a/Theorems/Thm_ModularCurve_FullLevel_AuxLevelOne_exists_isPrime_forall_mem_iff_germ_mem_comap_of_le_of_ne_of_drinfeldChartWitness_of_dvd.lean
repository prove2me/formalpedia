-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_isPrime_forall_mem_iff_germ_mem_comap_of_le_of_ne_of_drinfeldChartWitness_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.exists_isPrime_forall_mem_iff_germ_mem_comap_of_le_of_ne_of_drinfeldChartWitness_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/77e45de1-f043-5489-ab58-5b3915130b96
-- title:
--   Primes below a supersingular point come from Drinfeld-chart primes
-- statement:
--   Fix a prime $q$ and a positive integer $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic $0$ and $\zeta \in L$ a primitive $q$-th root of unity, and assume (`hι`) that there is a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the subgroup
--   $$H_1 = \ker\big((\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times\big) \cap \ker\big((\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell)^\times\big),$$
--   the first factor being [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), i.e. the units congruent to $1$ modulo $q$. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained as [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103), that is, generated over $L$ by the coefficientwise image of the $q$-expansion function field [`ModularCurve.xHFunctionField (q ^ 2 * M') H₁`](def/ModularCurve_XH.html#L79) of level $\Gamma_{H_1}(q^2M')$.
--
--   Let $A$ be a discrete valuation domain which is a henselian local ring with algebraically closed residue field, equipped with an $L$-algebra structure making $L$ its fraction field and compatible with an $A$-algebra structure on $K$ (`IsScalarTower A L K`), such that $q$ lies in $\mathfrak{m}_A$ and $\zeta$ lies in the image of $A$ in $L$. Let $\varpi$ be a generator of $\mathfrak{m}_A$, and let $\varpi_t \in A$ satisfy $\varpi_t^{\,q^2-1} = q u$ for some unit $u$ of $A$. Let $j \in K$ be nonzero with Laurent expansion equal to the image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81). Write $C =$ `chartAlgFin A ↥K j` for the $j$-finite chart algebra, i.e. the $A$-subalgebra of $K$ of elements integral over $A[j]$, and `jChartFin A ↥K j` for the element $j$ of $C$; let $\mathfrak{X} =$ [`AlgebraicCurve.TwoChartIntegralModel A ↥K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) be the two-chart integral model, the pushout of $\operatorname{Spec}$ of the two chart algebras along the middle chart, with structure morphism `toBase` to $\operatorname{Spec} A$ and with $\operatorname{Spec} C =$ `XFin A ↥K j` mapping in by `ιFin A ↥K j`.
--
--   Supersingular point data. Let $y \subset C$ be a maximal ideal containing the image of $\varpi$, and assume (`hss`) that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : C \to \Omega$ with kernel $y$ one has $\varphi(j) \in$ [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of those $j_0 \in \Omega$ such that every elliptic curve over $\Omega$ with $j$-invariant $j_0$ has no nonzero point killed by $q$. Let $z$ be a point of $\mathfrak{X}$ and let $\varpi_z$ be the germ at $z$ of the global section obtained from $\varpi$ via `toBase`, assumed to lie in the maximal ideal of the stalk $\mathcal{O}_{\mathfrak{X},z}$. Let $y'$ be a point of $\operatorname{Spec} C$ with `ιFin` image $z$, satisfying the same supersingularity condition (`hss'`) for its prime $y'.\mathrm{asIdeal}$, and assume $y'.\mathrm{asIdeal} = y$.
--
--   Drinfeld chart witness. Let $W_1$ be a complete discrete valuation domain (complete for the $\mathfrak{m}_{W_1}$-adic topology), $\sigma_1 : A \to W_1$ a ring homomorphism with $\mathfrak{m}_{W_1} = (\sigma_1\varpi)$, and $f_1, u_1, v_1 \in W_1[[X_0,X_1]]$ with $u_1, v_1$ units and
--   $$f_1 - \big(X_0X_1^q - X_0^qX_1\big) \in (X_0,X_1)^{q+2},$$
--   the subtracted term being [`DrinfeldCurve.LocalChart.drinfeldForm q W₁`](def/DrinfeldCurve_LocalChart.html#L18). Put $S = W_1[[X_0,X_1]]/\big(C(\sigma_1(\varpi_t^{\,q+1}))v_1 - f_1u_1\big)$ with quotient map $\mathrm{mk}_S$, write $\mathrm{STK} = \mathcal{O}_{\mathfrak{X},z}$, let $\mathrm{CMP}$ be its $\mathfrak{m}$-adic completion with structure map $\mathrm{toC} : \mathrm{STK} \to \mathrm{CMP}$, and let $e_1 : \mathrm{CMP} \xrightarrow{\ \sim\ } S$ be a ring isomorphism. Let $\mathrm{germ}_Y : C \to \mathrm{STK}$ be the canonical map, the composite of the inverses of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism and of the `ιFin`-chart isomorphism on the top open, followed by the germ at $z$ on the open image of `ιFin`.
--
--   The hypothesis `hW₁` is a conjunction of seven clauses about these data. (i) For all $a \in A$, the image of the germ at $z$ of $a$ (via `toBase`) in $S$ under $e_1 \circ \mathrm{toC}$ is $\mathrm{mk}_S(C(\sigma_1 a))$. (ii) For every $\gamma \in \Gamma_0(M')$ and every $\tau \in \operatorname{Aut}_L(K)$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29) — i.e. for all weights $k$, all modular forms $f,g$ of weight $k$ for $\Gamma_{H_1}(q^2M')$ with integral $q$-expansions $p_f,p_g$, $p_g$ having nonzero associated Laurent series, all $x \in K$ whose Laurent expansion is that of $p_f/p_g$, and all $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$, the identity $\iota_*(\tau x) \cdot (g \mid_k \delta)^\wedge = (f \mid_k \delta)^\wedge$ holds for $\delta$ the conjugate of $\gamma^{-1}$ by $\mathrm{diag}(q,1)$ as in `conjElemN` — the automorphism $\tau$ maps $C$ into $C$. (iii) For such $\gamma$ with $\gamma_{11} \equiv 1 \pmod{\ell}$ and such $\tau$, together with a proof $h_{\mathrm{pres}}$ that $\tau$ preserves $C$, the restriction of $\tau$ to $C$ is the identity modulo $y'.\mathrm{asIdeal}$. (iv) For such $\gamma$, $\tau$, $h_{\mathrm{pres}}$ with the restriction of $\tau$ congruent to the identity modulo $y'.\mathrm{asIdeal}$, there exist a ring automorphism $\theta$ of $S$, an element $c \in W_1$ and a matrix $M \in \mathrm{Mat}_2(W_1)$ such that: $\theta$ intertwines $e_1 \circ \mathrm{toC} \circ \mathrm{germ}_Y$ with the restriction of $\tau$; $\theta$ fixes $\mathrm{mk}_S(C(w))$ for all $w \in W_1$; $\theta(\mathrm{mk}_S X_{j}) \equiv \mathrm{mk}_S\big(\sum_i C(M_{ij})X_i\big)$ modulo the square of the ideal generated by $\mathrm{mk}_S X_0, \mathrm{mk}_S X_1$; $c^{q+1} \equiv 1$ and $M_{ij} \equiv c\,\gamma_{ij}$ modulo $\mathfrak{m}_{W_1}$; if $\gamma_{11} \equiv 1 \pmod \ell$ then $c \equiv 1$ modulo $\mathfrak{m}_{W_1}$; and if $\gamma \in \Gamma(q)$ and $\tau$ is not the identity on $K$ then $c - 1 \notin \mathfrak{m}_{W_1}$. (v) A separation clause: for integers $a_1,b_1,a_2,b_2$ and prime ideals $P_1,P_2$ of $S$, each omitting at least one of $\mathrm{mk}_S X_0, \mathrm{mk}_S X_1$, each containing $\mathrm{mk}_S(C(\sigma_1\varpi))$, and each containing an element $\mathrm{mk}_S(C(a_i)X_0 + C(b_i)X_1 + h)$ with $h \in (X_0,X_1)^2$, if $q \nmid a_1b_2 - a_2b_1$ then the contractions of $P_1$ and $P_2$ along $\mathrm{toC}$ followed by $e_1$ differ. (vi) For a prime $P$ of $S$ omitting one of $\mathrm{mk}_S X_0, \mathrm{mk}_S X_1$, containing $\mathrm{mk}_S(C(\sigma_1\varpi))$, and containing such an element with $(a,b) = (1,0)$: for $a \in C$, $\mathrm{toC}(\mathrm{germ}_Y a)$ lies in the contraction of $P$ along $e_1$ if and only if every Laurent coefficient of $a$ lies in the image of $\mathfrak{m}_A$ under $A \to L$. (vii) An existence clause: the element [`ModularCurve.jqNModC L q`](def/ModularCurve_JqCoeff.html#L18) lies in $K$ and in $C$, and there are $a_0 \in A$ with this element congruent to $a_0$ modulo $y'.\mathrm{asIdeal}$, an integer $e_0 \ge 1$ and $h \in (X_0,X_1)^{e_0}$ such that for all $a,b \in W_1$, at least one of which is a unit, with $a^qb - ab^q \in \mathfrak{m}_{W_1}$, the sum $\sum_{i=0}^{e_0} \mathrm{coeff}_{(i,\,e_0-i)}(h)\,a^ib^{e_0-i}$ is a unit, and $e_1\big(\mathrm{toC}(\mathrm{germ}_Y(\text{that element} - a_0))\big) = \mathrm{mk}_S(h)$.
--
--   Finally, let $\mathfrak{p} \subset C$ be a prime ideal containing the image of $\varpi$, with $\mathfrak{p} \le y$ and $\mathfrak{p} \ne y$.
--
--   Under these hypotheses the conclusion asserts the existence of an ideal $P$ of $S$ such that: $P$ is prime; at least one of $\mathrm{mk}_S X_0$, $\mathrm{mk}_S X_1$ does not lie in $P$; $\mathrm{mk}_S(C(\sigma_1\varpi)) \in P$; and for every $a \in C$ one has $a \in \mathfrak{p}$ if and only if $\mathrm{toC}(\mathrm{germ}_Y a)$ lies in the contraction of $P$ along $e_1$.
--
--   The statement identifies each prime of the $j$-finite chart algebra strictly below a supersingular maximal ideal $y$ and containing the uniformiser — geometrically, each component of the special fibre through the supersingular point $z$ — as the contraction of a branch prime of the completed Drinfeld chart $W_1[[X_0,X_1]]/(\varpi_t^{q+1}v_1 - f_1u_1)$ at $z$. It is proved from [`ModularCurve.FullLevel.AuxLevelOne.comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin_of_dvd`](thm.html#ModularCurve.FullLevel.AuxLevelOne.comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin_of_dvd), and feeds the counting and comparison of special-fibre components at supersingular points in the $\Gamma_1(\ell)$-diamond frame with $\ell \equiv 11 \pmod{12}$, $\ell \mid M'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_exists_isPrime_forall_mem_iff_germ_mem_comap_of_le_of_ne_of_drinfeldChartWitness_of_dvd.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevelOne.exists_isPrime_forall_mem_iff_germ_mem_comap_of_le_of_ne_of_drinfeldChartWitness_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})

    (ϖt : A) (hϖt : ∃ u : A, IsUnit u ∧ ϖt ^ (q ^ 2 - 1) = (q : A) * u)

    (y : Ideal ↥(chartAlgFin A (↥K) j)) (hy : y.IsMaximal) (hϖy : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω), RingHom.ker φ = y → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (hy'y : y'.asIdeal = y)
      (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
        [IsAdicComplete (IsLocalRing.maximalIdeal W₁) W₁] (σ₁ : A →+* W₁)
        (hσ₁ : IsLocalRing.maximalIdeal W₁ = Ideal.span {σ₁ ϖ})
        (f₁ u₁ v₁ : MvPowerSeries (Fin 2) W₁) (hu₁ : IsUnit u₁) (hv₁ : IsUnit v₁)
        (hf₁ : f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁ ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ (q + 2))
        (e₁ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})

    (hW₁ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e₁ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ₁ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W₁) (M : Matrix (Fin 2) (Fin 2) W₁),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e₁ (toC (germY a))) = e₁ (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W₁) ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W₁)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e₁ : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e₁ : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₁) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e₁ : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L q ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W₁, (a ∉ IsLocalRing.maximalIdeal W₁ ∨ b ∉ IsLocalRing.maximalIdeal W₁) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W₁ →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e₁ : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))
    (𝔭 : Ideal ↥(chartAlgFin A (↥K) j)) (h𝔭 : 𝔭.IsPrime) (hϖ𝔭 : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ 𝔭) (h𝔭y : 𝔭 ≤ y) (h𝔭ne : 𝔭 ≠ y) :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
        ∃ P : Ideal S, P.IsPrime ∧ (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) ∧
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P ∧
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            a ∈ 𝔭 ↔ toC (germY a) ∈ Ideal.comap (e₁ : CMP →+* S) P := by sorry
