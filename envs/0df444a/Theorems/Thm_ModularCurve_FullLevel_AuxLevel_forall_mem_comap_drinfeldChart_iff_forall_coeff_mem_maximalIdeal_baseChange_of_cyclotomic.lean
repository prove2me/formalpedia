-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_forall_mem_comap_drinfeldChart_iff_forall_coeff_mem_maximalIdeal_baseChange_of_cyclotomic
-- name    : ModularCurve.FullLevel.AuxLevel.forall_mem_comap_drinfeldChart_iff_forall_coeff_mem_maximalIdeal_baseChange_of_cyclotomic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/95d80527-bfcb-5dac-83a4-2b996d6e0ba8
-- title:
--   Base change of the Gauss-branch criterion on a Drinfeld chart
-- statement:
--   Throughout, $q$ is a prime with $5 \le q$, $M'$ a nonzero natural number not divisible by $q$, and $\ell$ a prime with $3 \le \ell$, $\ell \ne q$ and $\ell \nmid M'$.
--
--   **Data over $L$.** $L$ is a field of characteristic zero containing a primitive $q$-th root of unity $\zeta$ and a primitive $(q\ell)$-th root of unity $\xi$, and the hypothesis `hι` requires a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\xi) = \exp(2\pi i/(q\ell))$. $K$ is an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$, and `hK` identifies it with [`ModularCurve.laurentBaseChange L`](def/ModularCurve_LaurentCoeff.html#L103) applied to [`ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M')`](def/ModularCurve_XH.html#L79): that is, $K$ is the subfield of $\mathrm{LaurentSeries}\,L$ generated over $L$ by the coefficientwise image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the function field over $\mathbb{Q}$ of the modular curve of level $(q\ell)^2M'$ for the subgroup [`ModularCurve.FullLevel.levelH (q * ℓ) M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of the reduction map $(\mathbb{Z}/(q\ell)^2M')^\times \to (\mathbb{Z}/q\ell)^\times$.
--
--   **The discrete valuation ring $A$.** $A$ is a discrete valuation domain with $\mathrm{Frac}(A) = L$ and algebraically closed residue field, subject to: $q \in \mathfrak m_A$ (`hAq`), $\zeta$ lies in the image of $A$ (`hζA`), and $A$ acts on $K$ compatibly with the tower $A \to L \to K$. The element $j \in K$ has, by `hj`, image in $\mathrm{LaurentSeries}\,L$ equal to [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), the coefficientwise image of the $q$-expansion $q^{-1}\,j_{\mathrm{Num}}$ of the modular $j$-function, and $j \ne 0$. Finally $\varpi \in A$ generates $\mathfrak m_A$ (`hϖ`), and $t \in A$ satisfies $t^{q-1} = q\,w$ for some unit $w$ (`ht`).
--
--   **The point of the integral model over $A$.** [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) is the scheme obtained by gluing $\operatorname{Spec}$ of the two chart algebras $\mathrm{chartAlgFin} =$ the $A$-subalgebra of $K$ of elements integral over $A[j]$ and $\mathrm{chartAlgInf} =$ the elements integral over $A[j^{-1}]$. A point $z$ of this scheme is fixed, together with the element $\varpi z$ of the stalk at $z$ which, by `hϖz`, is the germ at $z$ of the global function obtained by pulling $\varpi$ back along [`AlgebraicCurve.TwoChartIntegralModel.toBase A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L258); the hypothesis `hz` places $\varpi z$ in the maximal ideal of the stalk, so $z$ lies in the special fibre. A point $y$ of `XFin` $= \operatorname{Spec}(\mathrm{chartAlgFin})$ is given with $\iota_{\mathrm{Fin}}(y) = z$ (`hy`). The hypothesis `hss` requires that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from the finite chart algebra to $\Omega$ with kernel exactly $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of those $j \in \Omega$ for which every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $j$ has no point $P \ne 0$ with $q \cdot P = 0$.
--
--   **The same data over the cyclotomic base.** $L_0$ is a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, with a primitive $q$-th root of unity $\zeta_0$ and a primitive $(q\ell)$-th root of unity $\xi_0$; $K_0 \subseteq \mathrm{LaurentSeries}\,L_0$ is the corresponding base-changed function field (`hK₀`); $A_0$ is a discrete valuation domain with fraction field $L_0$, with $q \in \mathfrak m_{A_0}$ (`hA₀q`), $\zeta_0$ in the image of $A_0$ (`hζ₀A`), acting on $K_0$ compatibly with the tower; $j_0 \in K_0$ has Laurent image the $q$-expansion of $j$ (`hj₀`) and is nonzero; $\varpi_0$ generates $\mathfrak m_{A_0}$ (`hϖ₀`). Points $z_0$, $y_0$, the germ $\varpi z_0$ of the pullback of $\varpi_0$, and the hypotheses `hϖz₀`, `hz₀`, `hy₀`, `hss₀` are the exact analogues of the data of the previous paragraph for $A_0$, $K_0$, $j_0$. No hypothesis on the residue field of $A_0$ is imposed.
--
--   **Comparison data.** A ring homomorphism $i : L_0 \to L$ carries $\zeta_0$ to $\zeta$ and $\xi_0$ to $\xi$; $A$ is an $A_0$-algebra by a local, injective structure map, compatible with $i$ in the sense that $\mathrm{algebraMap}\,A\,L \circ \mathrm{algebraMap}\,A_0\,A = i \circ \mathrm{algebraMap}\,A_0\,L_0$ (`hA₀A`), and $\varpi_0$ maps into $A$ to $t$ times a unit (`hϖ₀t`). A ring homomorphism $c_K : K_0 \to K$ acts coefficientwise by $i$ on Laurent expansions (`hcK`, via [`ModularCurve.coeffMap i`](def/ModularCurve_LaurentCoeff.html#L16)) and sends $j_0$ to $j$ (`hcKj`). A ring homomorphism $c$ between the finite chart algebras is compatible with $c_K$ (`hc`), and satisfies $c^{-1}(y) = y_0$ as prime ideals (`hcy`). Furthermore $\beta$ is a ring isomorphism $A \otimes_{A_0} \mathrm{chartAlgFin}(A_0,K_0,j_0) \cong \mathrm{chartAlgFin}(A,K,j)$ with $\beta(a \otimes b) = \mathrm{algebraMap}(a)\cdot c(b)$ (`hβ`).
--
--   **Drinfeld charts.** $W_0$ is a complete discrete valuation domain, $\sigma_0 : A_0 \to W_0$ a ring homomorphism with $\mathfrak m_{W_0} = (\sigma_0\varpi_0)$ (`hσ₀ϖ`). Power series $f_0, u_0, v_0 \in W_0[[X_0,X_1]]$ are given with $u_0, v_0$ units and $f_0 \equiv X_0X_1^q - X_0^qX_1$ modulo $(X_0,X_1)^{q+2}$, the subtrahend being [`DrinfeldCurve.LocalChart.drinfeldForm q W₀`](def/DrinfeldCurve_LocalChart.html#L18) (`hf₀`); $e_0$ is a ring isomorphism from the adic completion of the stalk at $z_0$ with respect to its maximal ideal onto $W_0[[X_0,X_1]]/(C(\sigma_0\varpi_0)v_0 - f_0u_0)$. On the other side, $\psi : W_0 \to \widehat{A} := \mathrm{AdicCompletion}(\mathfrak m_A)\,A$ satisfies $\psi \circ \sigma_0 = (\text{completion map}) \circ \mathrm{algebraMap}\,A_0\,A$ (`hψσ₀`); $f, u, v \in \widehat{A}[[X_0,X_1]]$ are arbitrary power series (no unit hypothesis is imposed on $u$, $v$); $e$ is a ring isomorphism from the adic completion of the stalk at $z$ onto $S := \widehat{A}[[X_0,X_1]]/(C(\hat t)v - fu)$, where $\hat t$ is the image of $t$; and `hrel` requires that the image under $\psi$, applied coefficientwise, of $C(\sigma_0\varpi_0)v_0 - f_0u_0$ lie in the ideal $(C(\hat t)v - fu)$.
--
--   **The anchor hypothesis over $A_0$ and the comparison hypotheses.** Write $S_0 := W_0[[X_0,X_1]]/(C(\sigma_0\varpi_0)v_0 - f_0u_0)$, $\mathrm{mkS}_0$ for its quotient map, $\mathrm{germY}_0$ for the canonical map from the finite chart algebra over $A_0$ to the stalk at $z_0$ (the germ at $z_0$ over the open image of $\iota_{\mathrm{Fin}}$, precomposed with the chart identifications), and $\mathrm{toC}_0$ for the map from that stalk to its adic completion. The hypothesis `hanchor₀` requires: for every prime ideal $P$ of $S_0$ with $\mathrm{mkS}_0(X_0) \notin P$ or $\mathrm{mkS}_0(X_1) \notin P$, containing $\mathrm{mkS}_0(C(\sigma_0\varpi_0))$, and containing $\mathrm{mkS}_0(C(1)X_0 + C(0)X_1 + h) = \mathrm{mkS}_0(X_0 + h)$ for some $h \in (X_0,X_1)^2$, and for every $a$ in the finite chart algebra over $A_0$: $\mathrm{toC}_0(\mathrm{germY}_0(a))$ lies in $e_0^{-1}(P)$ if and only if every Laurent coefficient of $a$, viewed in $\mathrm{LaurentSeries}\,L_0$, lies in the image of $\mathfrak m_{A_0}$ under $A_0 \to L_0$.
--
--   The hypothesis `hconst` requires that for every $a \in A$ the element $e$ assigns to the image in the completion of the germ at $z$ of the pullback of $a$ along `toBase` is the class of the constant series $C(\hat a)$ in $S$. The hypothesis `hcompat` requires that for all $x$ in the finite chart algebra over $A_0$ and all $s \in W_0[[X_0,X_1]]$: if $e_0$ sends the image in the completion of $\mathrm{germY}_0(x)$ to the class of $s$, then $e$ sends the image in the completion of $\mathrm{germY}(c(x))$ to the class of the coefficientwise $\psi$-image of $s$. Finally `hnoeth` requires the finite chart algebra $\mathrm{chartAlgFin}(A,K,j)$ to be Noetherian.
--
--   **Conclusion.** Write $S := \widehat{A}[[X_0,X_1]]/(C(\hat t)v - fu)$ with quotient map $\mathrm{mkS}$, $\mathrm{germY}$ for the canonical map from $\mathrm{chartAlgFin}(A,K,j)$ to the stalk at $z$, and $\mathrm{toC}$ for the map from that stalk to its adic completion. Then for every prime ideal $P$ of $S$ such that
--
--   1. $\mathrm{mkS}(X_0) \notin P$ or $\mathrm{mkS}(X_1) \notin P$;
--
--   2. $\mathrm{mkS}(C(\hat\varpi)) \in P$, the image of the uniformiser $\varpi$ of $A$;
--
--   3. there is $h \in (X_0,X_1)^2 \subseteq \widehat{A}[[X_0,X_1]]$ with $\mathrm{mkS}(C(1)X_0 + C(0)X_1 + h) \in P$, i.e. $\mathrm{mkS}(X_0+h) \in P$;
--
--   4. there is $h_0 \in (X_0,X_1)^2 \subseteq W_0[[X_0,X_1]]$ with $\mathrm{mkS}$ of the coefficientwise $\psi$-image of $C(1)X_0 + C(0)X_1 + h_0$ in $P$;
--
--   and for every $a$ in $\mathrm{chartAlgFin}(A,K,j)$: the element $\mathrm{toC}(\mathrm{germY}(a))$ lies in $e^{-1}(P)$ if and only if for every $n \in \mathbb{Z}$ there is $m \in \mathfrak m_A$ with $n$-th Laurent coefficient of $a$, taken in $\mathrm{LaurentSeries}\,L$, equal to the image of $m$ under $A \to L$.
--
--   This is the transport, from a cyclotomic base $(L_0, A_0)$ to a base change $(L, A)$, of the identification of the prime ideal cut out on a $j$-finite chart algebra by a branch prime of a Drinfeld chart (in the sense of the local description of the Igusa components through the supersingular points, Katz–Mazur) with the "Gauss" ideal of functions all of whose $q$-expansion coefficients lie in the maximal ideal of the base. It is used in the construction of the isomorphism of the completed local ring of the integral model at such a point with a Drinfeld-chart quotient of a two-variable power series ring over a base change with algebraically closed residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_forall_mem_comap_drinfeldChart_iff_forall_coeff_mem_maximalIdeal_baseChange_of_cyclotomic.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AdicCompletionLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups TensorProduct

theorem ModularCurve.FullLevel.AuxLevel.forall_mem_comap_drinfeldChart_iff_forall_coeff_mem_maximalIdeal_baseChange_of_cyclotomic
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

    (L₀ : Type) [Field L₀] [CharZero L₀] [IsCyclotomicExtension {q * ℓ} ℚ L₀]
    (ζ₀ : L₀) (hζ₀ : IsPrimitiveRoot ζ₀ q)
    (ξ₀ : L₀) (hξ₀ : IsPrimitiveRoot ξ₀ (q * ℓ))
    (K₀ : IntermediateField L₀ (LaurentSeries L₀))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L₀
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [Algebra A₀ L₀] [IsFractionRing A₀ L₀]
    (hA₀q : (q : A₀) ∈ IsLocalRing.maximalIdeal A₀) (hζ₀A : ∃ x : A₀, algebraMap A₀ L₀ x = ζ₀)
    [Algebra A₀ ↥K₀] [IsScalarTower A₀ L₀ ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L₀)) = ModularCurve.coeffEmb L₀ ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ϖ₀ : A₀) (hϖ₀ : IsLocalRing.maximalIdeal A₀ = Ideal.span {ϖ₀})
    (z₀ : ↥(AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀))
    (ϖz₀ : (AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)
    (hϖz₀ : ϖz₀ = ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ ⊤ z₀ trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A₀ (↥K₀) j₀).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom ϖ₀)))
    (hz₀ : ϖz₀ ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
    (y₀ : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A₀ (↥K₀) j₀))
    (hy₀ : (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀ = z₀)
    (hss₀ : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* Ω),
      RingHom.ker φ = y₀.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A₀ (↥K₀) j₀) ∈ ModularCurve.ssJSet q Ω)

    (i : L₀ →+* L) (hiζ : i ζ₀ = ζ) (hiξ : i ξ₀ = ξ)
    [Algebra A₀ A] [IsLocalHom (algebraMap A₀ A)] (hinj : Function.Injective (algebraMap A₀ A))
    (hA₀A : ∀ a : A₀, algebraMap A L (algebraMap A₀ A a) = i (algebraMap A₀ L₀ a))
    (hϖ₀t : ∃ w : A, IsUnit w ∧ algebraMap A₀ A ϖ₀ = t * w)
    (cK : ↥K₀ →+* ↥K)
    (hcK : ∀ x : ↥K₀, ((cK x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap i ((x : ↥K₀) : LaurentSeries L₀))
    (hcKj : cK j₀ = j)
    (c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hc : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
      ((c a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = cK (a : ↥K₀))
    (hcy : Ideal.comap c y.asIdeal = y₀.asIdeal)

    (β : (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) ≃+*
      ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hβ : ∀ (a : A) (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)),
      β (a ⊗ₜ[A₀] b) = algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a * c b)

    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀] (σ₀ : A₀ →+* W₀)
    (hσ₀ϖ : IsLocalRing.maximalIdeal W₀ = Ideal.span {σ₀ ϖ₀})
    (f₀ u₀ v₀ : MvPowerSeries (Fin 2) W₀) (hu₀ : IsUnit u₀) (hv₀ : IsUnit v₀)
    (hf₀ : f₀ - DrinfeldCurve.LocalChart.drinfeldForm q W₀ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ (q + 2))
    (e₀ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀) ≃+*
      MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})

    (ψ : W₀ →+* (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (hψσ₀ : ∀ a : A₀, ψ (σ₀ a) = (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (algebraMap A₀ A a))
    (f u v : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
        MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})

    (hrel : MvPowerSeries.map ψ (MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀) ∈
      Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})

    (hanchor₀ :
      let STK₀ := ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)
      let CMP₀ := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
      let toC₀ : STK₀ →+* CMP₀ := algebraMap STK₀ CMP₀
      let S₀ := (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})
      let mkS₀ : MvPowerSeries (Fin 2) W₀ →+* S₀ := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})
      let germY₀ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* STK₀ :=
        ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)

      (∀ P : Ideal S₀, P.IsPrime → (mkS₀ (MvPowerSeries.X 0) ∉ P ∨ mkS₀ (MvPowerSeries.X 1) ∉ P) →
        mkS₀ (MvPowerSeries.C (σ₀ ϖ₀)) ∈ P →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ 2,
            mkS₀ (MvPowerSeries.C (1 : W₀) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₀) * MvPowerSeries.X 1 + h) ∈ P) →
        ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
          toC₀ (germY₀ a) ∈ Ideal.comap (e₀ : CMP₀ →+* S₀) P ↔
            ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A₀,
              (((a : ↥K₀) : LaurentSeries L₀).coeff n) = algebraMap A₀ L₀ m))

    (hconst :
      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
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
        Ideal.Quotient.mk _ (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) a))))

    (hcompat :
      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ (x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) (s : MvPowerSeries (Fin 2) W₀),
        e₀ (algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
          ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)) x)) =
          Ideal.Quotient.mk _ s →
        e (toC (germY (c x))) = mkS (MvPowerSeries.map ψ s)))

    (hnoeth : IsNoetherianRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) :
      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
        mkS (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ϖ)) ∈ P →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A)), MvPowerSeries.X 1}) ^ 2,
            mkS (MvPowerSeries.C (1 : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) * MvPowerSeries.X 1 + h) ∈ P) →

        (∃ h₀ ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ 2,
            mkS (MvPowerSeries.map ψ (MvPowerSeries.C (1 : W₀) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₀) * MvPowerSeries.X 1 + h₀)) ∈ P) →
        ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
          toC (germY a) ∈ Ideal.comap (e : CMP →+* S) P ↔
            ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
              (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) := by sorry
