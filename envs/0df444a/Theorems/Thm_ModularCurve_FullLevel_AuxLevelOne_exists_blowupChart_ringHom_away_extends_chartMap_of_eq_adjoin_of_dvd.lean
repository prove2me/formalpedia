-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_blowupChart_ringHom_away_extends_chartMap_of_eq_adjoin_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.exists_blowupChart_ringHom_away_extends_chartMap_of_eq_adjoin_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/fe5dc4b1-4fca-5763-8c1a-3c024ac4e7d5
-- title:
--   Extension of the chart map to the affine blow-up algebra
-- statement:
--   Throughout, $q$ is a prime, $M'$ a non-zero natural number with $q \nmid M'$, and $\ell$ a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$.
--
--   **Level and function field.** $L$ is a field of characteristic zero, $\zeta \in L$ a primitive $q$-th root of unity, and `hι` asserts the existence of a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = \exp(2\pi i/q)$. The subgroup $H_1 \le (\mathbb{Z}/q^2M')^\times$ is required by `hH₁` to be the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of the reduction map $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, with the kernel of the reduction map $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell)^\times$ (the latter coming from $\ell \mid M' \mid q^2 M'$); thus $H_1$ consists of the units congruent to $1$ modulo $q$ and modulo $\ell$. The intermediate field $K$ of $L \subseteq L((t))$ is required by `hK` to be [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield of $L((t))$ generated over $L$ by the coefficientwise image, under the map [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) induced by $\mathbb{Q} \to L$, of the $q$-expansion function field [`ModularCurve.xHFunctionFieldC ℚ (q ^ 2 * M') H₁`](def/ModularCurve_XH.html#L76) attached to $\Gamma_{H_1}(q^2M') \subseteq \mathbb{Q}((t))$.
--
--   **Base ring.** $A$ is a discrete valuation domain which is a Henselian local ring with algebraically closed residue field, equipped with an $A$-algebra structure on $L$ making $L$ a fraction field of $A$, such that $q$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A \to L$; $K$ is an $A$-algebra compatibly with $A \to L \to K$. Further, $\varpi \in A$ generates the maximal ideal of $A$ (`hϖ`), and $\varpi_t \in A$ satisfies $\varpi_t^{\,q^2-1} = q\,u$ for some unit $u$ (`hϖt`). The element $j \in K$ is non-zero and its image in $L((t))$ is the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), the Laurent series $t^{-1}$ times the power series [`ModularCurve.jNumQ`](def/ModularCurve_X0.html#L149) over $\mathbb{Q}$. Finally, `inst` provides an algebra structure of the field `GaloisField q 2` with $q^2$ elements on the residue field of $A$.
--
--   **Chart algebra and the supersingular point.** Write $C :=$ `chartAlgFin A ↥K j`, the $A$-subalgebra of $K$ consisting of those elements that are integral over $A[j]$, and `jChartFin A ↥K j` for $j$ regarded as an element of $C$. The ideal $y$ of $C$ is maximal (`hy`) and contains the image of $\varpi$ (`hϖy`). The hypothesis `hss` requires that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : C \to \Omega$ with kernel $y$, the element $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), that is: every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $\varphi(j)$ has trivial $q$-torsion ($q \cdot P = 0$ implies $P = 0$ for affine points $P$).
--
--   **Point of the two-chart model.** [`AlgebraicCurve.TwoChartIntegralModel A ↥K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) is the pushout of the two morphisms $\operatorname{Spec}$ of the inclusions of $C$ and of `chartAlgInf A ↥K j` (the elements of $K$ integral over $A[j^{-1}]$) into the middle chart, with its canonical morphism `toBase` to $\operatorname{Spec} A$. Here $z$ is a point of this scheme, $\varpi_z$ is the germ at $z$ of the global section obtained from $\varpi$ along `toBase` (`hϖz`), and `hz` requires $\varpi_z$ to lie in the maximal ideal of the stalk at $z$. The point $y'$ of `XFin A ↥K j` $= \operatorname{Spec} C$ is mapped to $z$ by `ιFin` (`hy'`), its ideal is $y$ (`hy'y`), and `hss'` repeats the supersingularity requirement of `hss` for the ideal `y'.asIdeal`.
--
--   **Drinfeld chart witness.** $W_1$ is a discrete valuation domain, a domain complete for the adic topology of its maximal ideal, together with a ring homomorphism $\sigma_1 : A \to W_1$ such that $\sigma_1(\varpi)$ generates the maximal ideal of $W_1$ (`hσ₁`). Elements $f_1, u_1, v_1 \in W_1[\![X_0,X_1]\!]$ are given with $u_1, v_1$ units and with $f_1 - (X_0X_1^q - X_0^qX_1)$ in $(X_0,X_1)^{q+2}$ (`hf₁`, where $X_0X_1^q - X_0^qX_1$ is [`DrinfeldCurve.LocalChart.drinfeldForm q W₁`](def/DrinfeldCurve_LocalChart.html#L18)). Finally $e_1$ is a ring isomorphism from the adic completion of the stalk at $z$ with respect to its maximal ideal onto
--   $$S := W_1[\![X_0,X_1]\!]\big/\big(\,C(\sigma_1(\varpi_t^{\,q+1}))\,v_1 - f_1 u_1\,\big).$$
--
--   **The blow-up algebra.** $J$ is an ideal of $C$, and $B$ is an $A$-subalgebra of $K$ required by `hB` to be the $C$-subalgebra of $K$ generated by $\{x \in K : \exists\, i \in J,\ x \cdot \varpi_t = i\}$, viewed as an $A$-subalgebra; $C \le B$ is recorded by `hCB`. Thus $B = C[J/\varpi_t]$.
--
--   **Chart map.** In the hypotheses `hbridge`, `hcentre` and in the conclusion the following abbreviations are introduced: $\mathrm{STK}$ is the stalk at $z$, $\mathrm{CMP}$ its adic completion with respect to its maximal ideal, $\mathrm{toC}$ the canonical map $\mathrm{STK} \to \mathrm{CMP}$, $S$ the quotient above, $\mathrm{mkS}$ the quotient map $W_1[\![X_0,X_1]\!] \to S$, and $\mathrm{germY} : C \to \mathrm{STK}$ the composite of the inverses of the $\Gamma$–$\operatorname{Spec}$ isomorphism for $C$ and of the isomorphism identifying $C$ with the sections over the image open `ιFin ''ᵁ ⊤` with the germ map at $z$ (legitimate since `ιFin` carries $y'$ to $z$). Write $\Psi := e_1 \circ \mathrm{toC} \circ \mathrm{germY} : C \to S$ and $\mathfrak{m}_S := (\mathrm{mkS}\,C(\sigma_1\varpi), \mathrm{mkS}\,X_0, \mathrm{mkS}\,X_1)$.
--
--   The hypothesis `hbridge` is the conjunction of: the contraction of $\mathfrak{m}_S$ along $\Psi$ is $y$; for every $n$ and every $s \in S$ there is $a \in C$ with $\Psi(a) - s \in \mathfrak{m}_S^{\,n}$; $\Psi(a) = \mathrm{mkS}(C(\sigma_1 a))$ for all $a \in A$; every $c \in C$ is congruent modulo $y$ to the image of some $a \in A$; every $w \in W_1$ is congruent modulo the maximal ideal of $W_1$ to $\sigma_1(a)$ for some $a \in A$; the contraction of the maximal ideal of $W_1$ along $\sigma_1$ is the maximal ideal of $A$; $\mathfrak{m}_S$ is maximal and is the only maximal ideal of $S$; and $S$ is flat over $C$ for the algebra structure given by $\Psi$.
--
--   The hypothesis `hcentre` is the conjunction of: the ideal of $S$ generated by the image of $J$ under $\Psi$ equals $(\mathrm{mkS}\,C(\sigma_1\varpi_t), \mathrm{mkS}\,X_0, \mathrm{mkS}\,X_1)$; there is an ideal $I$ of $C$ with $J$ equal to the intersection of $I$ with the contraction along $\Psi$ of that ideal, and $I + y = C$; $J \le y$; and the image of $\varpi_t$ in $C$ lies in $J$.
--
--   **Conclusion.** Let $L_{\mathrm{loc}} :=$ `Localization.Away (mkS (MvPowerSeries.C (σ₁ ϖt)))` with structure map $\iota_S : S \to L_{\mathrm{loc}}$, put
--   $$x_0 := \iota_S(\mathrm{mkS}\,X_0)\cdot \mathrm{invSelf},\qquad x_1 := \iota_S(\mathrm{mkS}\,X_1)\cdot \mathrm{invSelf},$$
--   where $\mathrm{invSelf}$ is the inverse in $L_{\mathrm{loc}}$ of $\mathrm{mkS}(C(\sigma_1\varpi_t))$, and let $R_{\mathrm{loc}} \le L_{\mathrm{loc}}$ be the subring generated by the image of $\iota_S$ together with $x_0$ and $x_1$. Then there exists a ring homomorphism $\Phi : B \to L_{\mathrm{loc}}$, together with the facts that $\iota_S(s) \in R_{\mathrm{loc}}$ for all $s \in S$, that $x_0 \in R_{\mathrm{loc}}$, that $x_1 \in R_{\mathrm{loc}}$, and that $\Phi(b) \in R_{\mathrm{loc}}$ for all $b \in B$, such that:
--
--   (i) $\Phi$ restricted to $C$ (via $C \le B$) is $\iota_S \circ \Psi$, i.e. $\Phi(a) = \iota_S(\Psi(a))$ for every $a \in C$;
--
--   (ii) for all $x \in B$ and $i \in C$ with $i \in J$ and $x\,\varpi_t = i$ in $K$, one has $\Phi(x)\cdot \iota_S(\mathrm{mkS}(C(\sigma_1\varpi_t))) = \iota_S(\Psi(i))$;
--
--   (iii) $\sigma_1(\varpi_t) \neq 0$;
--
--   (iv) $\mathrm{mkS}(C(\sigma_1\varpi_t))$ is a non-zero-divisor in $S$.
--
--   This is the extension step for the affine blow-up algebra $B = C[J/\varpi_t]$ of the chart algebra $C$ along the centre $J$: the chart map $\Psi : C \to S$ into the Drinfeld local model $S$ at the supersingular point $z$ is extended to $B$ with values in the subring $S[X_0/\sigma_1\varpi_t, X_1/\sigma_1\varpi_t]$ of the localisation of $S$ away from $\sigma_1\varpi_t$, the generators of $J$ being divided by $\varpi_t$. It is used by [`ModularCurve.FullLevel.AuxLevelOne.exists_blowupChart_ringHom_localBlowupChart_surjective_ker_eq_span_of_dense_of_flat_of_dvd`](thm.html#ModularCurve.FullLevel.AuxLevelOne.exists_blowupChart_ringHom_localBlowupChart_surjective_ker_eq_span_of_dense_of_flat_of_dvd), where this extension is upgraded to a surjection onto the local blow-up chart with identified kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_exists_blowupChart_ringHom_away_extends_chartMap_of_eq_adjoin_of_dvd.lean

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

theorem ModularCurve.FullLevel.AuxLevelOne.exists_blowupChart_ringHom_away_extends_chartMap_of_eq_adjoin_of_dvd
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
    (J : Ideal ↥(chartAlgFin A (↥K) j))
    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)
    (hCB : chartAlgFin A (↥K) j ≤ B)

    (hbridge :
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

        Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY)) (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) = y ∧

        (∀ (n : ℕ) (s : S), ∃ a : ↥(chartAlgFin A (↥K) j), ((e₁ : CMP →+* S).comp (toC.comp germY)) a - s ∈ (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ n) ∧

        (∀ a : A, ((e₁ : CMP →+* S).comp (toC.comp germY)) (algebraMap A ↥(chartAlgFin A (↥K) j) a) = mkS (MvPowerSeries.C (σ₁ a))) ∧

        (∀ c : ↥(chartAlgFin A (↥K) j), ∃ a : A, c - algebraMap A ↥(chartAlgFin A (↥K) j) a ∈ y) ∧
        (∀ w : W₁, ∃ a : A, w - σ₁ a ∈ IsLocalRing.maximalIdeal W₁) ∧
        Ideal.comap σ₁ (IsLocalRing.maximalIdeal W₁) = IsLocalRing.maximalIdeal A ∧

        (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}).IsMaximal ∧ (∀ I : Ideal S, I.IsMaximal → I = Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ∧

        (letI : Algebra ↥(chartAlgFin A (↥K) j) S := (((e₁ : CMP →+* S).comp (toC.comp germY))).toAlgebra
         Module.Flat ↥(chartAlgFin A (↥K) j) S))

    (hcentre :
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

        Ideal.map ((e₁ : CMP →+* S).comp (toC.comp germY)) J = Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} ∧

        (∃ I : Ideal ↥(chartAlgFin A (↥K) j),
            J = Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY)) (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ⊓ I ∧ I ⊔ y = ⊤) ∧
        J ≤ y ∧ algebraMap A ↥(chartAlgFin A (↥K) j) ϖt ∈ J)
    (inst : Algebra (GaloisField q 2) (ResidueField A)) :
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
        let Lloc := Localization.Away (mkS (MvPowerSeries.C (σ₁ ϖt)))
        let ιS : S →+* Lloc := algebraMap S Lloc
        let x₀ : Lloc := ιS (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))
        let x₁ : Lloc := ιS (mkS (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))
        let Rloc : Subring Lloc := Subring.closure (Set.range ιS ∪ {x₀, x₁})
        ∃ (Φ : ↥B →+* Lloc) (hιR : ∀ s : S, ιS s ∈ Rloc) (hx₀ : x₀ ∈ Rloc) (hx₁ : x₁ ∈ Rloc) (hΦR : ∀ b : ↥B, Φ b ∈ Rloc),

          (∀ a : ↥(chartAlgFin A (↥K) j), Φ ⟨(a : ↥K), hCB a.2⟩ = ιS (((e₁ : CMP →+* S).comp (toC.comp germY)) a)) ∧
          (∀ (x : ↥B) (i : ↥(chartAlgFin A (↥K) j)), i ∈ J → (x : ↥K) * algebraMap A ↥K ϖt = (i : ↥K) →
              Φ x * ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) = ιS (((e₁ : CMP →+* S).comp (toC.comp germY)) i)) ∧

          σ₁ ϖt ≠ 0 ∧ mkS (MvPowerSeries.C (σ₁ ϖt)) ∈ nonZeroDivisors S := by sorry
