-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_inertia_drinfeldChart_linearPart_diagOneElem_of_semilinear_of_drinfeldChartWitness_linearPart_riders_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.inertia_drinfeldChart_linearPart_diagOneElem_of_semilinear_of_drinfeldChartWitness_linearPart_riders_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/20c6f021-80ea-565a-af84-36e8f5ae0570
-- title:
--   Linear part of semilinear inertia on an anchored Drinfeld chart
-- statement:
--   **Arithmetic data.** Fix a prime $q$, a nonzero natural number $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, let $\zeta \in L$ be a primitive $q$-th root of unity, $\xi \in L$ a primitive $q\ell$-th root of unity, and assume $\zeta = \xi^{\ell}$. Let $H_1 \le (\mathbb{Z}/q^2M')^{\times}$ be the subgroup [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22) $\cap$ $\ker\big((\mathbb{Z}/q^2M')^{\times} \to (\mathbb{Z}/\ell)^{\times}\big)$, where `levelH q M'` is the kernel of the reduction $(\mathbb{Z}/q^2M')^{\times} \to (\mathbb{Z}/q)^{\times}$ and the second kernel is taken for the divisibility $\ell \mid q^2M'$ coming from $\ell \mid M'$; so $H_1$ consists of the units congruent to $1$ modulo $q$ and modulo $\ell$. Let $K$ be the intermediate field of $L \subseteq L((t))$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield generated over $L$ by the image, under the coefficientwise map [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) induced by $\mathbb{Q} \to L$, of the $q$-expansion function field of $\Gamma_{H_1}(q^2M')$.
--
--   Let $A$ be a discrete valuation domain with an $L$-algebra structure making $L$ its fraction field, with $q \in \mathfrak{m}_A$ and with $\zeta$ in the image of $A \to L$, and let $K$ carry an $A$-algebra structure compatible with that of $L$ (scalar tower). Let $j \in K$ be the element whose Laurent expansion is [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), the $q$-expansion $t^{-1}\cdot(\text{integral } j\text{-series})$ of the modular invariant, with $j \neq 0$, and let $\varpi$ generate $\mathfrak{m}_A$.
--
--   **Geometric data.** Write $X$ for [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), the scheme obtained as the pushout gluing $\operatorname{Spec}$ of `chartAlgFin`, the ring of elements of $K$ integral over $A[j]$, to $\operatorname{Spec}$ of `chartAlgInf`, the ring of elements of $K$ integral over $A[j^{-1}]$, and `toBase` for its structure morphism to $\operatorname{Spec} A$. Let $z$ be a point of $X$, let $\varpi_z$ be the germ at $z$ of the global section of $X$ obtained from $\varpi$ through `toBase`, assumed to lie in the maximal ideal of the stalk of $X$ at $z$, and let $y$ be a point of `XFin` $= \operatorname{Spec}$ `chartAlgFin` with $\iota_{\mathrm{Fin}}(y) = z$. The hypothesis `hss` asserts supersingularity at $y$: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi :$ `chartAlgFin` $\to \Omega$ with kernel the prime $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), i.e. for every elliptic curve $W$ over $\Omega$ with $j$-invariant $\varphi(j)$ the only point $P$ of $W$ with $q \cdot P = 0$ is $0$.
--
--   **Chart witness.** Let $W$ be a discrete valuation domain which is a domain and complete for its maximal-ideal-adic topology, let $\sigma : A \to W$ be a ring homomorphism with $\mathfrak{m}_W = (\sigma\varpi)$, and let $f, u, v \in W[[X_0,X_1]]$ with $u, v$ units and
--   $$f - (X_0X_1^{q} - X_0^{q}X_1) \in (X_0,X_1)^{q+2},$$
--   the subtracted form being [`DrinfeldCurve.LocalChart.drinfeldForm q W`](def/DrinfeldCurve_LocalChart.html#L18). Let $e$ be a ring isomorphism from the $\mathfrak{m}$-adic completion of the stalk of $X$ at $z$ onto
--   $$S := W[[X_0,X_1]]\big/\big(C(\sigma\varpi)\,v - f\,u\big).$$
--   Throughout, `STK` denotes that stalk, `CMP` its adic completion, `toC` the canonical map `STK` $\to$ `CMP`, `mkS` the quotient map $W[[X_0,X_1]] \to S$, and `germY` the canonical homomorphism from `chartAlgFin` to `STK` (the germ at $z$ over the open image of $\iota_{\mathrm{Fin}}$, composed with the identifications of global sections of $\operatorname{Spec}$ `chartAlgFin`).
--
--   Three clauses on this witness are assumed.
--
--   *Constants* (`hconst`): for every $a \in A$, the composite of $e$ with `toC` applied to the germ at $z$ of the section coming from $a$ through `toBase` equals `mkS` $(C(\sigma a))$.
--
--   *Level-equivariant linear parts* (`hlin`): for every $\gamma \in SL_2(\mathbb{Z})$ lying in $\Gamma_0(M')$, every $L$-algebra automorphism $\tau$ of $K$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29) — the condition that, for every weight $k$, every pair $f, g$ of modular forms for $\Gamma_{H_1}(q^2M')$ with integral $q$-expansions $p_f, p_g$ and $p_g \neq 0$ as a series over $\mathbb{Q}$, every $x \in K$ whose Laurent expansion is the coefficientwise image of $p_f/p_g$, and every embedding $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$, the $\iota$-image of the Laurent expansion of $\tau x$ times the $q$-expansion of $g \mid_k \mathrm{conjElemN}\, q\, \gamma^{-1}$ equals the $q$-expansion of $f \mid_k \mathrm{conjElemN}\, q\, \gamma^{-1}$ — and every proof `hpres` that $\tau$ maps `chartAlgFin` into itself, if the induced endomorphism of `chartAlgFin` is congruent to the identity modulo the prime $y$, then there exist a ring automorphism $\theta$ of $S$, an element $c \in W$ and a matrix $M \in M_2(W)$ such that: $\theta$ is induced by $\tau$ through $e \circ$ `toC` $\circ$ `germY`; $\theta$ fixes `mkS` $(C(w))$ for every $w \in W$; for each $j$, $\theta(\mathrm{mkS}\,X_j) - \mathrm{mkS}\big(\sum_i C(M_{ij})X_i\big)$ lies in the square of the ideal generated by $\mathrm{mkS}\,X_0$ and $\mathrm{mkS}\,X_1$; $c^{q+1} - 1 \in \mathfrak{m}_W$; $M_{ij} - c\,\gamma_{ij} \in \mathfrak{m}_W$ for all $i,j$; if $\gamma_{11} \equiv 1 \pmod{\ell}$ then $c - 1 \in \mathfrak{m}_W$; and if $\gamma \in \Gamma(q)$ and $\tau$ is not the identity on $K$ then $c - 1 \notin \mathfrak{m}_W$.
--
--   *Branch anchor* (`hanchor`): for every prime ideal $P$ of $S$ which does not contain both $\mathrm{mkS}\,X_0$ and $\mathrm{mkS}\,X_1$, contains $\mathrm{mkS}\,(C(\sigma\varpi))$, and contains $\mathrm{mkS}(C(1)X_0 + C(0)X_1 + h)$ for some $h \in (X_0,X_1)^2$, and for every $a \in$ `chartAlgFin`: the element `toC (germY a)` lies in the preimage of $P$ under $e$ if and only if for every $n \in \mathbb{Z}$ the $n$-th Laurent coefficient of $a$ is the image of some element of $\mathfrak{m}_A$.
--
--   **Conclusion.** Under these hypotheses, for every $d \in (\mathbb{Z}/q)^{\times}$, every ring automorphism $\sigma_L$ of $L$ and every ring automorphism $\sigma_A$ of $A$ such that $\sigma_A$ is compatible with $\sigma_L$ along $A \to L$, such that $\sigma_A a - a \in \mathfrak{m}_A$ for all $a \in A$, and such that $\sigma_L\zeta = \zeta^{\,(d : \mathbb{Z}/q).\mathrm{val}}$; for every ring automorphism $\tau$ of $K$ which acts on Laurent expansions coefficientwise by $\sigma_L$, for every proof `hpres` that $\tau$ maps `chartAlgFin` into itself, assuming in addition that $\tau^{-1}$ maps `chartAlgFin` into itself and that the endomorphism of `chartAlgFin` induced by $\tau$ is congruent to the identity modulo the prime $y$; and for every ring automorphism $\theta$ of $S$ and ring automorphism $\sigma_W$ of $W$ such that $\theta$ is induced by $\tau$ through $e \circ$ `toC` $\circ$ `germY`, such that $\sigma_W \circ \sigma = \sigma \circ \sigma_A$ on $A$, such that $\sigma_W w - w \in \mathfrak{m}_W$ for all $w \in W$, and such that $\theta(\mathrm{mkS}\,(C(w))) = \mathrm{mkS}\,(C(\sigma_W w))$ for all $w \in W$: there exists a matrix $M \in M_2(W)$ with the following two properties.
--
--   First, $M$ is a linear part of $\theta$: for each index $j \in \{0,1\}$,
--   $$\theta(\mathrm{mkS}\,X_j) - \mathrm{mkS}\Big(\sum_{i} C(M_{ij})\,X_i\Big) \in \big(\mathrm{mkS}\,X_0,\ \mathrm{mkS}\,X_1\big)^2 .$$
--
--   Second, the reduction of $M$ modulo $\mathfrak{m}_W$ is the diagonal matrix prescribed by the cyclotomic character value $d$: for all $i, j \in \{0,1\}$,
--   $$M_{ij} - \Big(\big(d \cdot (\mathrm{diagOneElem}\, q\, (d^{q})^{-1})_{ij}\big).\mathrm{val}\Big) \in \mathfrak{m}_W,$$
--   where [`ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹`](def/ModularCurve_FullLevelJacobian.html#L233) is the element $\mathrm{diag}\big(1, (d^{q})^{-1}\big)$ of $GL_2(\mathbb{Z}/q)$, the product is formed in $\mathbb{Z}/q$ entrywise, and the natural-number lift `ZMod.val` of each entry is mapped into $W$. Since $d^{q-1} = 1$ in $(\mathbb{Z}/q)^{\times}$, the prescribed matrix is $\mathrm{diag}(d,1)$.
--
--   This is the local computation at a supersingular point of the two-chart integral model of the modular curve attached to $H_1 \le (\mathbb{Z}/q^2M')^\times$: on a Drinfeld chart $W[[X_0,X_1]]/(C(\sigma\varpi)v - fu)$ anchored along one branch, an automorphism coming from inertia acting on coefficients by $\sigma_L$ with cyclotomic value $d$ has linear part congruent to $\mathrm{diag}(d,1)$ modulo $\mathfrak{m}_W$. It is the variant of the computation adapted to the auxiliary guard prime $\ell \equiv 11 \pmod{12}$, valid without any lower bound on $q$, and it feeds the statement [`ModularCurve.FullLevel.AuxLevelOne.inertia_drinfeldChart_semilinear_linearPart_diagOneElem_of_linearPart_riders_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd`](thm.html#ModularCurve.FullLevel.AuxLevelOne.inertia_drinfeldChart_semilinear_linearPart_diagOneElem_of_linearPart_riders_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_inertia_drinfeldChart_linearPart_diagOneElem_of_semilinear_of_drinfeldChartWitness_linearPart_riders_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevelOne.inertia_drinfeldChart_linearPart_diagOneElem_of_semilinear_of_drinfeldChartWitness_linearPart_riders_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hζξ : ζ = ξ ^ ℓ)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
      [IsAdicComplete (IsLocalRing.maximalIdeal W) W] (σ : A →+* W)
      (hσϖ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
      (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
      (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
      (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
        MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})

    (hconst :

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))))
    (hlin :

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal) →
              ∃ (θ : S ≃+* S) (c : W) (M : Matrix (Fin 2) (Fin 2) W),

                (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                  θ (e (toC (germY a))) = e (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                    mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                  (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W) ∧
                (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W) ∈ IsLocalRing.maximalIdeal W) ∧
                (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W) ∧

                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W)))
    (hanchor :

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
        mkS (MvPowerSeries.C (σ ϖ)) ∈ P →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
            mkS (MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h) ∈ P) →
        ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
          toC (germY a) ∈ Ideal.comap (e : CMP →+* S) P ↔
            ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
              (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m))
    :

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
      ∀ (d : (ZMod q)ˣ) (σL : L ≃+* L) (σA : A ≃+* A),

        (∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a)) →

        (∀ a : A, σA a - a ∈ IsLocalRing.maximalIdeal A) →

        σL ζ = ζ ^ ((d : ZMod q).val) →
        ∀ τ : ↥K ≃+* ↥K,

          (∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L)) →
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),

            (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ.symm a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) →

            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal)) →

            ∀ (θ : S ≃+* S) (σW : W ≃+* W),

              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                θ (e (toC (germY a))) = e (toC (germY ((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) →

              (∀ a : A, σW (σ a) = σ (σA a)) →
              (∀ w : W, σW w - w ∈ IsLocalRing.maximalIdeal W) →
              (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C (σW w))) →
              ∃ M : Matrix (Fin 2) (Fin 2) W,

                (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                    mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                  (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧

                (∀ ii jj : Fin 2, M ii jj -
                    ((((d : ZMod q) * ((ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹ : CuspidalType.GL2 q) :
                        Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val : ℕ) : W) ∈ IsLocalRing.maximalIdeal W) := by sorry
