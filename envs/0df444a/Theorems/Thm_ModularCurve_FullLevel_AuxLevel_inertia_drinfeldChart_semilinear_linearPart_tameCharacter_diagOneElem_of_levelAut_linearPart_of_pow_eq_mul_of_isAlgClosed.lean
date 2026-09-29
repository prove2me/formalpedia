-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_inertia_drinfeldChart_semilinear_linearPart_tameCharacter_diagOneElem_of_levelAut_linearPart_of_pow_eq_mul_of_isAlgClosed
-- name    : ModularCurve.FullLevel.AuxLevel.inertia_drinfeldChart_semilinear_linearPart_tameCharacter_diagOneElem_of_levelAut_linearPart_of_pow_eq_mul_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/c754e423-7b7c-5086-9519-60ddff1a44ad
-- title:
--   Tame inertia on the completed Drinfeld chart, general constants
-- statement:
--   **Arithmetic data.** Let $q$ be a prime with $5 \le q$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $\ell$ be a prime with $3 \le \ell$, $\ell \ne q$ and $\ell \nmid M'$. Let $L$ be a field of characteristic zero containing a primitive $q$-th root of unity $\zeta$ and a primitive $(q\ell)$-th root of unity $\xi$, and assume `hι`: there is a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\xi) = \exp(2\pi i/(q\ell))$. Let $K$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ subject to `hK`: $K$ is [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103) of the subfield [`ModularCurve.xHFunctionField ((q*ℓ)^2*M') (ModularCurve.FullLevel.levelH (q*ℓ) M')`](def/ModularCurve_XH.html#L79) of $\mathrm{LaurentSeries}\,\mathbb{Q}$, that is, $K$ is the intermediate field generated over $L$ by the coefficientwise image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) (the map induced by $\mathbb{Q} \to L$) of the $q$-expansion function field of level $\Gamma_H$ with $N_0 = (q\ell)^2 M'$ and $H =$ `levelH (q*ℓ) M'` the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^\times \to (\mathbb{Z}/q\ell)^\times$.
--
--   **Base ring and integral model.** Let $A$ be a discrete valuation domain with $A \subseteq L$ as an $A$-algebra having $L$ as fraction field, with algebraically closed residue field, such that $q \in \mathfrak{m}_A$ (`hAq`) and $\zeta$ lies in the image of $A$ (`hζA`); let $K$ be an $A$-algebra compatibly with $L$. Let $j \in K$ be the element whose Laurent series is [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), the $q$-expansion of the modular $j$-function, with $j \ne 0$, and let $\varpi \in A$ satisfy $\mathfrak{m}_A = (\varpi)$. Let $t \in A$ satisfy `ht`: $t^{q-1} = q\,w$ for some unit $w$ of $A$. Write $\mathfrak{X} =$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), the pushout of the two affine charts $\mathrm{Spec}$ of `chartAlgFin` (the elements of $K$ integral over $A[j]$) and of `chartAlgInf` (those integral over $A[j^{-1}]$) along the common middle chart, together with its structure morphism `toBase` to $\mathrm{Spec}\,A$.
--
--   **The point.** Let $z$ be a point of $\mathfrak{X}$ and let $\varpi z$ be the germ at $z$ of the global section of $\mathcal{O}_{\mathfrak{X}}$ obtained from $\varpi$ through `toBase` (`hϖz`), and assume $\varpi z$ lies in the maximal ideal of the stalk at $z$ (`hz`), so that $z$ lies in the fibre over $q$. Let $y$ be a point of $\mathrm{Spec}$ `chartAlgFin A K j` mapping to $z$ under `ιFin` (`hy`). The hypothesis `hss` requires supersingularity at $y$: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from `chartAlgFin A K j` to $\Omega$ with kernel the prime $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), i.e. every elliptic Weierstrass curve over $\Omega$ with that $j$-invariant has no nonzero point killed by $q$.
--
--   **Drinfeld chart data.** Let $W$ be a discrete valuation domain, adically complete for its maximal ideal, let $\sigma : A \to W$ be a ring homomorphism with $\mathfrak{m}_W = (\sigma\varpi)$ (`hσϖ`), and let $f, u, v \in W[[X_0,X_1]]$ with $u$, $v$ units and $f$ congruent to [`DrinfeldCurve.LocalChart.drinfeldForm q W`](def/DrinfeldCurve_LocalChart.html#L18) $= X_0X_1^q - X_0^qX_1$ modulo $(X_0,X_1)^{q+2}$ (`hf`). Let $e$ be a ring isomorphism from the adic completion of the stalk $\mathcal{O}_{\mathfrak{X},z}$ for its maximal ideal onto $S := W[[X_0,X_1]]/(C(\sigma t)\,v - f\,u)$.
--
--   The statement abbreviates: `STK` the stalk at $z$, `CMP` its adic completion, `toC` the canonical map `STK → CMP`, $S$ and `mkS` the quotient ring and its quotient map, and `germY` the canonical ring homomorphism from `chartAlgFin A K j` to `STK` obtained from the germ at $z$ on the open image of `ιFin` composed with the identifications of sections over that image with the chart algebra.
--
--   **Standing hypothesis (constants).** For every $a \in A$, the image under $e$ of the class in `CMP` of the germ at $z$ of $a$ (through `toBase`) is the class of the constant series $C(\sigma a)$.
--
--   **Standing hypothesis (level equivariance).** For every $\gamma \in SL(2,\mathbb{Z})$ lying in $\Gamma_0(M')$, every $L$-algebra automorphism $\tau$ of $K$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt L (q*ℓ) ξ (q*ℓ) ((q*ℓ)^2*M') (levelH (q*ℓ) M') γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29) — that is, for all weights $k$, all modular forms $f_0, g_0$ of weight $k$ for the level subgroup $\Gamma_H$ with integral $q$-expansions $p_f, p_g$, $p_g$ having nonzero associated Laurent series, every $x \in K$ whose Laurent series is $p_f/p_g$, and every embedding $\iota : L \to \mathbb{C}$ with $\iota(\xi) = \exp(2\pi i/(q\ell))$, the coefficientwise image under $\iota$ of the Laurent series of $\tau x$ times the $q$-expansion of $g_0 \mid_k$ `conjElemN (q*ℓ) γ⁻¹` equals the $q$-expansion of $f_0 \mid_k$ `conjElemN (q*ℓ) γ⁻¹`, where `conjElemN m δ` is the real matrix $\begin{pmatrix} \delta_{00} & \delta_{01}/m \\ m\,\delta_{10} & \delta_{11}\end{pmatrix}$ — and every proof `hpres` that $\tau$ maps `chartAlgFin A K j` into itself, if the restriction of $\tau$ to the chart algebra satisfies $\tau(a) - a \in y$ for all $a$, then there exist a ring automorphism $\theta$ of $S$, an element $c \in W$ and a matrix $M \in \mathrm{Mat}_2(W)$ such that: $\theta \circ e \circ$ `toC` $\circ$ `germY` agrees with $e \circ$ `toC` $\circ$ `germY` $\circ \tau$ on the chart algebra; $\theta$ fixes the class of every constant $C(w)$, $w \in W$; for each $jj$, $\theta(X_{jj}) - \sum_{ii} M_{ii\,jj} X_{ii}$ lies in the square of the ideal generated by the classes of $X_0, X_1$; $c^{q+1} - 1 \in \mathfrak{m}_W$; $M_{ii\,jj} \equiv c\,\gamma_{ii\,jj} \pmod{\mathfrak{m}_W}$ for all $ii, jj$; if $\gamma \in \Gamma(\ell)$ then $c - 1 \in \mathfrak{m}_W$; and if $\gamma \in \Gamma(q)$ and $\tau$ is not the identity on $K$ then $c - 1 \notin \mathfrak{m}_W$.
--
--   **Conclusion.** Under these hypotheses, for every $d \in (\mathbb{Z}/q)^\times$, every ring automorphism $\sigma_L$ of $L$ and every ring automorphism $\sigma_A$ of $A$ such that $\sigma_A$ is compatible with $\sigma_L$ along $A \to L$ and $\sigma_A(a) - a \in \mathfrak{m}_A$ for all $a \in A$, for every $\pi \in A$ with $\pi^{q^2-1} = q$, every $\tilde\alpha \in A$ with $\sigma_A\pi = \tilde\alpha\,\pi$ and $\tilde\alpha^{q+1} - (d.\mathrm{val} : A) \in \mathfrak{m}_A$, and every ring automorphism $\tau$ of $K$ acting on Laurent series by applying $\sigma_L$ to coefficients (i.e. the Laurent series of $\tau x$ is [`ModularCurve.coeffMap σL`](def/ModularCurve_LaurentCoeff.html#L16) of that of $x$, for all $x \in K$), the following hold.
--
--   First, $\tau$ maps `chartAlgFin A K j` into itself. Secondly, for every proof `hpres` of that preservation: the restriction of $\tau$ to the chart algebra satisfies $\tau(a) - a \in y$ for all $a$; and there exist a ring automorphism $\theta$ of $S$, a ring automorphism $\sigma_W$ of $W$, an element $\tilde c \in W$ and a matrix $M \in \mathrm{Mat}_2(W)$ such that
--
--   1. $\theta(e(\mathrm{toC}(\mathrm{germY}(a)))) = e(\mathrm{toC}(\mathrm{germY}(\tau a)))$ for every $a$ in the chart algebra;
--
--   2. $\sigma_W \circ \sigma = \sigma \circ \sigma_A$ on $A$;
--
--   3. $\sigma_W(w) - w \in \mathfrak{m}_W$ for all $w \in W$;
--
--   4. $\theta$ carries the class of $C(w)$ to the class of $C(\sigma_W w)$, for all $w \in W$;
--
--   5. for each $jj$, $\theta(X_{jj}) - \sum_{ii} C(M_{ii\,jj})X_{ii}$ lies in the square of the ideal of $S$ generated by the classes of $X_0$ and $X_1$;
--
--   6. $\tilde c - \sigma(\tilde\alpha^{q+1}) \in \mathfrak{m}_W$;
--
--   7. for all $ii, jj$, $M_{ii\,jj} - \tilde c \cdot \lambda_{ii\,jj} \in \mathfrak{m}_W$, where $\lambda_{ii\,jj} \in W$ is the image of the canonical natural-number representative of the $(ii,jj)$ entry of the matrix $\begin{pmatrix} 1 & 0 \\ 0 & (d^q)^{-1}\end{pmatrix}$ over $\mathbb{Z}/q$, namely [`ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹`](def/ModularCurve_FullLevelJacobian.html#L233).
--
--   Thus the linear part of $\theta$ is, modulo $\mathfrak{m}_W$, the scalar $\tilde c \equiv \sigma(\tilde\alpha^{q+1})$ times $\mathrm{diag}(1, d^{-q})$.
--
--   This is the general-constants form of the computation of the tame inertia action on the completed local ring of the integral model at a supersingular point, read through a Drinfeld chart: a coefficientwise automorphism of $K$ inducing an inertial automorphism of the constants acts semilinearly on $W[[X_0,X_1]]/(C(\sigma t)v - fu)$, with linear part a scalar congruent to $\sigma(\tilde\alpha^{q+1})$ times $\mathrm{diag}(1,d^{-q})$, so that inertia moves the Drinfeld coordinates only through the cyclotomic value $d = \tilde\alpha^{q+1}$. It is used in the assembly of supersingular affine charts with linked scalars and linked inertia for the modular curve of level $(q\ell)^2M'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_inertia_drinfeldChart_semilinear_linearPart_tameCharacter_diagOneElem_of_levelAut_linearPart_of_pow_eq_mul_of_isAlgClosed.lean

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

theorem ModularCurve.FullLevel.AuxLevel.inertia_drinfeldChart_semilinear_linearPart_tameCharacter_diagOneElem_of_levelAut_linearPart_of_pow_eq_mul_of_isAlgClosed
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (t : A) (ht : ∃ w : A, IsUnit w ∧ t ^ (q - 1) = (q : A) * w)
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
      MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ t) * v - f * u}) :

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ t) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ t) * v - f * u})
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
        Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) →

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

                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W)) →

    ∀ (d : (ZMod q)ˣ) (σL : L ≃+* L) (σA : A ≃+* A),
      (∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a)) →

      (∀ a : A, σA a - a ∈ IsLocalRing.maximalIdeal A) →

      ∀ (π : A), π ^ (q ^ 2 - 1) = (q : A) → ∀ (αt : A), σA π = αt * π →
      αt ^ (q + 1) - (((d : ZMod q).val : ℕ) : A) ∈ IsLocalRing.maximalIdeal A →
      ∀ τ : ↥K ≃+* ↥K,

        (∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L)) →

        (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
          τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧
        ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
            τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),

          (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            (((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal)) ∧

          ∃ (θ : S ≃+* S) (σW : W ≃+* W) (ct : W) (M : Matrix (Fin 2) (Fin 2) W),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              θ (e (toC (germY a))) = e (toC (germY ((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧
            (∀ a : A, σW (σ a) = σ (σA a)) ∧
            (∀ w : W, σW w - w ∈ IsLocalRing.maximalIdeal W) ∧
            (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C (σW w))) ∧
            (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
              (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧

            (ct - σ (αt ^ (q + 1)) ∈ IsLocalRing.maximalIdeal W) ∧
            (∀ ii jj : Fin 2, M ii jj -
                ct * (((((ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹ : CuspidalType.GL2 q) :
                    Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val : ℕ) : W) ∈ IsLocalRing.maximalIdeal W) := by sorry
