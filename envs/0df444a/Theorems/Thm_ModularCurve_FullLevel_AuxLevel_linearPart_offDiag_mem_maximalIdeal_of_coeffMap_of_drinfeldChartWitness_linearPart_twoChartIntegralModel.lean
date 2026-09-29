-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_linearPart_offDiag_mem_maximalIdeal_of_coeffMap_of_drinfeldChartWitness_linearPart_twoChartIntegralModel
-- name    : ModularCurve.FullLevel.AuxLevel.linearPart_offDiag_mem_maximalIdeal_of_coeffMap_of_drinfeldChartWitness_linearPart_twoChartIntegralModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/e4f45560-0f81-5d3b-b8ec-31e0a83c6c17
-- title:
--   Off-diagonal linear part of an inertial automorphism lies in mathfrak m_W
-- statement:
--   Setting. Fix a prime $q \ge 5$, a positive integer $M'$ with $q \nmid M'$, and a prime $\ell \ge 3$ with $\ell \ne q$ and $\ell \nmid M'$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb Q$ of type $\{q\ell\}$, let $\zeta \in L$ be a primitive $q$-th root of unity and $\xi \in L$ a primitive $q\ell$-th root of unity. Let $K$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ which, by the hypothesis `hK`, is [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M'))`](def/ModularCurve_LaurentCoeff.html#L103): the subfield of $L((t))$ generated over $L$ by the coefficientwise images of the Fourier-expansion function field of level $\Gamma_H$ with $N_0 = (q\ell)^2 M'$ and $H =$ `levelH (q * ℓ) M'`, the kernel of the reduction $(\mathbb Z/(q\ell)^2M')^\times \to (\mathbb Z/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$.
--
--   Let $A$ be a discrete valuation ring which is a domain with fraction field $L$, such that $q \in \mathfrak m_A$ (`hAq`) and $\zeta$ lies in the image of $A \to L$ (`hζA`), and let $K$ carry an $A$-algebra structure compatible with $A \to L \to K$. Let $j \in K$ have Laurent expansion [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), the coefficientwise image in $L((t))$ of the expansion of the modular invariant $j$ over $\mathbb Q$ (`hj`), with $j \ne 0$. Let $\varpi \in A$ be a uniformiser, $\mathfrak m_A = (\varpi)$ (`hϖ`).
--
--   Geometric data. Let $X :=$ [`AlgebraicCurve.TwoChartIntegralModel A (↥K) j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), the pushout of the two maps from $\operatorname{Spec}$ of the compositum chart to $\operatorname{Spec}$ of the $A$-subalgebras of $K$ consisting of the elements integral over $A[j]$, respectively over $A[j^{-1}]$. Let $z$ be a point of $X$, and let $\varpi_z$ be the element of the stalk $\mathcal O_{X,z}$ obtained as the germ at $z$ of the image of $\varpi$ under the structure morphism $X \to \operatorname{Spec} A$ (`hϖz`); it is assumed that $\varpi_z \in \mathfrak m_{\mathcal O_{X,z}}$ (`hz`), so $z$ lies in the special fibre. Let $y$ be a point of `XFin A (↥K) j`, the spectrum of the chart algebra $\mathcal A :=$ `chartAlgFin A (↥K) j`, with image $z$ under the canonical map (`hy`). The supersingularity hypothesis `hss` requires: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : \mathcal A \to \Omega$ with kernel the prime $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), that is, every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $\varphi(j)$ has no non-zero point killed by $q$.
--
--   Chart data. Let $W$ be a complete discrete valuation ring which is a domain, $\sigma : A \to W$ a ring homomorphism with $\mathfrak m_W = (\sigma \varpi)$ (`hσϖ`), and let $f, u, v \in W[[X_0, X_1]]$ with $u$ and $v$ units (`hu`, `hv`) and
--   $$f - (X_0X_1^q - X_0^qX_1) \in (X_0, X_1)^{q+2}$$
--   (`hf`), the subtracted term being [`DrinfeldCurve.LocalChart.drinfeldForm q W`](def/DrinfeldCurve_LocalChart.html#L18). Let $e$ be a ring isomorphism from the $\mathfrak m$-adic completion of $\mathcal O_{X,z}$ onto $S := W[[X_0,X_1]]/(C(\sigma\varpi)\,v - f\,u)$. Write `toC` for the canonical map $\mathcal O_{X,z} \to$ its completion, `mkS` for the quotient map onto $S$, and `germY` for the ring homomorphism $\mathcal A \to \mathcal O_{X,z}$ given by the germ at $z$ over the open image of $\operatorname{Spec}\mathcal A$ in $X$.
--
--   The hypothesis `hconst` states that $e$ matches the base: for every $a \in A$, the element $e(\mathrm{toC}(\text{germ of the image of } a))$ is the class of the constant $C(\sigma a)$ in $S$.
--
--   The hypothesis `hlin` (level-equivariance with its numerical clauses, summarised here) states: for every $\gamma \in SL_2(\mathbb Z)$ lying in $\Gamma_0(M')$, every $L$-algebra automorphism $\tau$ of $K$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M') γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29) — i.e. for all weights $k$, all modular forms $f_1, g_1$ of level $\Gamma_H$ with integral Fourier expansions $p_f, p_g$, $p_g$ having non-zero image, every $x \in K$ whose Laurent expansion is the coefficientwise image of $p_f/p_g$, and every embedding $\iota : L \to \mathbb C$ with $\iota \xi = \exp(2\pi i/q\ell)$, the identity $\iota_*(\tau x)\cdot (\text{expansion of } g_1 \mid_k \mathrm{conjElemN}(q\ell)(\gamma^{-1})) = (\text{expansion of } f_1 \mid_k \mathrm{conjElemN}(q\ell)(\gamma^{-1}))$ holds — every proof that $\tau$ maps $\mathcal A$ into $\mathcal A$, and under the assumption that $\tau$ is trivial at $y$ (for all $a \in \mathcal A$, $\tau a - a \in y$), there exist a ring automorphism $\theta$ of $S$, an element $c \in W$ and a matrix $M \in M_2(W)$ such that $\theta$ corresponds to $\tau$ under $e \circ \mathrm{toC}\circ \mathrm{germY}$; $\theta$ fixes all constant classes; for each $jj$, $\theta(\mathrm{mkS}(X_{jj})) - \mathrm{mkS}(\sum_{ii} C(M_{ii\,jj})X_{ii})$ lies in the square of the ideal generated by $\mathrm{mkS}(X_0), \mathrm{mkS}(X_1)$; $c^{q+1} - 1 \in \mathfrak m_W$; $M_{ii\,jj} \equiv c\,\gamma_{ii\,jj} \pmod{\mathfrak m_W}$ for all $ii, jj$; if $\gamma \in \Gamma(\ell)$ then $c - 1 \in \mathfrak m_W$; and if $\gamma \in \Gamma(q)$ and $\tau$ is not the identity on $K$ then $c - 1 \notin \mathfrak m_W$.
--
--   Conclusion. Under these hypotheses, with the abbreviations above, the following holds. Let $\sigma_L$ be a ring automorphism of $L$ and $\sigma_A$ a ring automorphism of $A$ such that $\sigma_L$ restricts to $\sigma_A$ along $A \to L$, and such that $\sigma_A a - a \in \mathfrak m_A$ for all $a \in A$. Let $\tau$ be a ring automorphism of $K$ acting coefficientwise through $\sigma_L$, i.e. the Laurent expansion of $\tau x$ is [`ModularCurve.coeffMap σL`](def/ModularCurve_LaurentCoeff.html#L16) applied to that of $x$, for all $x \in K$; let `hpres` be any proof that $\tau$ maps $\mathcal A$ into $\mathcal A$, assume in addition that $\tau^{-1}$ maps $\mathcal A$ into $\mathcal A$, and that the induced endomorphism of $\mathcal A$ is trivial at $y$, that is $\tau a - a \in y$ for all $a \in \mathcal A$. Let $\theta$ be a ring automorphism of $S$ and $\sigma_W$ a ring automorphism of $W$ such that: $\theta$ corresponds to the restriction of $\tau$ to $\mathcal A$ under $e \circ \mathrm{toC} \circ \mathrm{germY}$; $\sigma_W \circ \sigma = \sigma \circ \sigma_A$ on $A$; $\sigma_W w - w \in \mathfrak m_W$ for all $w \in W$; and $\theta(\mathrm{mkS}(C(w))) = \mathrm{mkS}(C(\sigma_W w))$ for all $w \in W$, so that $\theta$ is $\sigma_W$-semilinear on constants. Finally let $M \in M_2(W)$ be such that for each $jj \in \{0,1\}$,
--   $$\theta(\mathrm{mkS}(X_{jj})) - \mathrm{mkS}\Big(\sum_{ii} C(M_{ii\,jj})X_{ii}\Big) \in \big(\mathrm{mkS}(X_0), \mathrm{mkS}(X_1)\big)^2 .$$
--   Then
--   $$M_{0\,1} \in \mathfrak m_W .$$
--
--   This is the off-diagonal vanishing statement for the linear part of a semilinear (inertial) automorphism of a Drinfeld-type chart at a supersingular point of the two-chart integral model of the modular curve of level $\Gamma_H$ with $N_0 = (q\ell)^2M'$: modulo $\mathfrak m_W$ the linear part is lower triangular, so the branch cut out by the lower unipotent level automorphisms is preserved. It is used by [`ModularCurve.FullLevel.AuxLevel.inertia_drinfeldChart_linearPart_diagOneElem_of_semilinear_of_drinfeldChartWitness_linearPart_riders_twoChartIntegralModel`](thm.html#ModularCurve.FullLevel.AuxLevel.inertia_drinfeldChart_linearPart_diagOneElem_of_semilinear_of_drinfeldChartWitness_linearPart_riders_twoChartIntegralModel), which pins down the reduction of the whole linear part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_linearPart_offDiag_mem_maximalIdeal_of_coeffMap_of_drinfeldChartWitness_linearPart_twoChartIntegralModel.lean

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

theorem ModularCurve.FullLevel.AuxLevel.linearPart_offDiag_mem_maximalIdeal_of_coeffMap_of_drinfeldChartWitness_linearPart_twoChartIntegralModel
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
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
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
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
                (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal W) ∧

                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W)))
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
      ∀ (σL : L ≃+* L) (σA : A ≃+* A),

        (∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a)) →

        (∀ a : A, σA a - a ∈ IsLocalRing.maximalIdeal A) →
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
              ∀ M : Matrix (Fin 2) (Fin 2) W,

                (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                    mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                  (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) →
                M 0 1 ∈ IsLocalRing.maximalIdeal W := by sorry
