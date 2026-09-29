-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_inertia_drinfeldChart_baseChange_semilinear_linearPart_of_cyclotomicWitness_inertia_of_isAlgClosed_of_isPrimitiveRoot_mul_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.inertia_drinfeldChart_baseChange_semilinear_linearPart_of_cyclotomicWitness_inertia_of_isAlgClosed_of_isPrimitiveRoot_mul_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/fba57c6b-9bf4-5fc0-98c2-5e9b21baec0c
-- title:
--   Base change of a cyclotomic Drinfeld-chart inertia witness
-- statement:
--   Throughout, $q$ is a prime, $M'$ a nonzero natural number with $q \nmid M'$, and $\ell$ a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$.
--
--   **Level and function field.** $H_1$ is a subgroup of $(\mathbb{Z}/q^2M')^\times$ required by `hH₁` to be the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22) — the kernel of the reduction of units `ZMod.unitsMap (dvd_sq_mul q M')` out of $(\mathbb{Z}/q^2M')^\times$ — with the kernel of the reduction of units $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell)^\times$ attached to the divisibility $\ell \mid q^2M'$ coming from $\ell \mid M'$. For a field $L$ of characteristic zero, `K` is required by `hK` to be [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)`](def/ModularCurve_LaurentCoeff.html#L103), that is the intermediate field of $L((t))$ (Laurent–Hahn series over $L$) generated over $L$ by the image, under the coefficientwise embedding [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81), of the rational $q$-expansion function field of $\Gamma_{H_1}(q^2M')$.
--
--   **Constants on the general side.** $L$ carries a primitive $q$-th root of unity $\zeta$ (`hζ`) and a primitive $(q\ell)$-th root of unity $\xi$ (`hξ`) with $\zeta = \xi^{\ell}$ (`hζξ`), and `hι` asserts the existence of a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\xi) = \exp(2\pi i/(q\ell))$. $A$ is a discrete valuation domain with fraction field $L$ whose residue field is algebraically closed, with $q$ in its maximal ideal (`hAq`) and $\zeta$ in the image of $A$ (`hζA`); $A$ acts on $K$ compatibly with the tower $A \to L \to K$. The element $j \in K$ is nonzero and has Laurent expansion [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81) (`hj`), the $q$-expansion of the modular $j$-invariant. $\varpi$ generates the maximal ideal of $A$ (`hϖ`), and $t \in A$ satisfies $t^{q-1} = q w$ for some unit $w$ (`ht`).
--
--   **Geometric data on the general side.** [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) is the scheme obtained by gluing $\operatorname{Spec}$ of the two chart algebras `chartAlgFin A K j` (the elements of $K$ integral over $A[j]$) and `chartAlgInf A K j` (the elements integral over $A[j^{-1}]$) along the middle chart. A point $z$ of this scheme is given, together with the element $\varpi z$ of the stalk at $z$ defined (`hϖz`) as the germ at $z$ of the global section obtained from $\varpi$ along the structure morphism `TwoChartIntegralModel.toBase A K j` to $\operatorname{Spec} A$; `hz` requires $\varpi z$ to lie in the maximal ideal of the stalk. A point $y$ of `XFin A K j = Spec (chartAlgFin A K j)` is given with `ιFin A K j` carrying $y$ to $z$ (`hy`). The hypothesis `hss` is a supersingularity condition at $y$: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from `chartAlgFin A K j` to $\Omega$ with kernel `y.asIdeal`, the value $\varphi(\mathrm{jChartFin})$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), i.e. every elliptic curve over $\Omega$ with that $j$-invariant has no non-zero point killed by $q$.
--
--   **The cyclotomic side.** $L_0$ is a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ for $\{q\ell\}$, with a primitive $q$-th root of unity $\zeta_0$ and a primitive $(q\ell)$-th root of unity $\xi_0$; $K_0$ is the same Laurent base change over $L_0$ (`hK₀`); $A_0$ is a discrete valuation domain with fraction field $L_0$, with $q$ in its maximal ideal (`hA₀q`) and $\zeta_0$ in the image of $A_0$ (`hζ₀A`), acting on $K_0$ compatibly with the tower; $j_0 \in K_0$ is non-zero with the same $q$-expansion (`hj₀`); $\varpi_0$ generates the maximal ideal of $A_0$ (`hϖ₀`). Exactly as above, a point $z_0$, the germ $\varpi z_0$ of $\varpi_0$ in the stalk at $z_0$ (`hϖz₀`) lying in the maximal ideal (`hz₀`), a point $y_0$ of `XFin A₀ K₀ j₀` above $z_0$ (`hy₀`), and the supersingularity condition `hss₀` at $y_0$ are given.
--
--   **Comparison data.** A ring homomorphism $i : L_0 \to L$ with $i(\zeta_0) = \zeta$ and $i(\xi_0) = \xi$; an $A_0$-algebra structure on $A$ for which $A_0 \to A$ is local and injective (`hinj`) and compatible with $i$ on fraction fields (`hA₀A`), with $\varpi_0$ mapping to $t$ up to a unit of $A$ (`hϖ₀t`); a ring homomorphism $c_K : K_0 \to K$ acting coefficientwise by $i$ on Laurent expansions (`hcK`) and sending $j_0$ to $j$ (`hcKj`); a ring homomorphism $c$ between the finite chart algebras compatible with $c_K$ (`hc`) and such that the contraction of `y.asIdeal` along $c$ is `y₀.asIdeal` (`hcy`); and a ring isomorphism $\beta : A \otimes_{A_0} \mathrm{chartAlgFin}(A_0,K_0,j_0) \to \mathrm{chartAlgFin}(A,K,j)$ with $\beta(a \otimes b) = a \cdot c(b)$ (`hβ`).
--
--   **The cyclotomic Drinfeld-chart witness.** $W_0$ is a discrete valuation domain, complete for the adic topology of its maximal ideal, together with a ring homomorphism $\sigma_0 : A_0 \to W_0$ such that the maximal ideal of $W_0$ is generated by $\sigma_0(\varpi_0)$ (`hσ₀ϖ`). Power series $f_0, u_0, v_0 \in W_0[[X_0,X_1]]$ are given with $u_0, v_0$ units and $f_0$ congruent to [`DrinfeldCurve.LocalChart.drinfeldForm q W₀`](def/DrinfeldCurve_LocalChart.html#L18) $= X_0X_1^q - X_0^qX_1$ modulo $(X_0,X_1)^{q+2}$ (`hf₀`), and $e_0$ is a ring isomorphism from the adic completion of the stalk at $z_0$ (with respect to its maximal ideal) onto $S_0 = W_0[[X_0,X_1]]/(C(\sigma_0\varpi_0)v_0 - f_0u_0)$. Writing $\mathrm{germY}_0$ for the canonical homomorphism from `chartAlgFin A₀ K₀ j₀` to the stalk at $z_0$ (the germ at $z_0$ on the open image of `ιFin A₀ K₀ j₀`), $\mathrm{toC}_0$ for the map to the adic completion, and $\mathrm{mkS}_0$ for the quotient map onto $S_0$, two hypotheses are imposed:
--
--   `hconst₀` (constants): for every $a \in A_0$, $e_0$ carries the image in the completion of the germ of $a$ along `toBase` to the class of $C(\sigma_0 a)$.
--
--   `hinert₀` (cyclotomic tame inertia): for every $d \in (\mathbb{Z}/q)^\times$, every $\sigma_L \in \operatorname{Aut}(L_0)$ and $\sigma_A \in \operatorname{Aut}(A_0)$ compatible on fraction fields, with $\sigma_A(a) - a$ in the maximal ideal of $A_0$ for all $a$, and with $\sigma_L(\zeta_0) = \zeta_0^{\,(d : \mathbb{Z}/q).\mathrm{val}}$, and for every ring automorphism $\tau$ of $K_0$ acting coefficientwise by $\sigma_L$: first, $\tau$ maps `chartAlgFin A₀ K₀ j₀` into itself; and secondly, for every proof `hpres` of that stability, writing $\tau|$ for the induced automorphism of the chart algebra, one has $\tau|(a) - a \in y_0.\mathrm{asIdeal}$ for all chart-algebra elements $a$, and there exist a ring automorphism $\theta$ of $S_0$, a ring automorphism $\sigma_W$ of $W_0$ and a matrix $M \in \mathrm{Mat}_2(W_0)$ such that $\theta \circ e_0 \circ \mathrm{toC}_0 \circ \mathrm{germY}_0 = e_0 \circ \mathrm{toC}_0 \circ \mathrm{germY}_0 \circ \tau|$; $\sigma_W \circ \sigma_0 = \sigma_0 \circ \sigma_A$; $\sigma_W(w) - w$ lies in the maximal ideal of $W_0$ for all $w$; $\theta(\mathrm{mkS}_0(C(w))) = \mathrm{mkS}_0(C(\sigma_W w))$ for all $w$; for each index $jj$, $\theta(\mathrm{mkS}_0(X_{jj})) - \mathrm{mkS}_0\big(\sum_{ii} C(M_{ii,jj})X_{ii}\big)$ lies in the square of the ideal generated by the classes of $X_0, X_1$; and every entry $M_{ii,jj}$ is congruent, modulo the maximal ideal of $W_0$, to the image in $W_0$ of the natural-number representative of the $(ii,jj)$ entry of $(d : \mathbb{Z}/q)$ times the matrix of [`ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹`](def/ModularCurve_FullLevelJacobian.html#L233), i.e. of $\mathrm{diag}(1, (d^q)^{-1})$ in $\mathrm{GL}_2(\mathbb{Z}/q)$.
--
--   **Transfer data on the general side.** Let $\hat{A}$ denote the adic completion of $A$ at its maximal ideal. A ring homomorphism $\psi : W_0 \to \hat{A}$ is given, together with $f, u, v \in \hat{A}[[X_0,X_1]]$, $u$ and $v$ units, with $f$ congruent to $X_0X_1^q - X_0^qX_1$ modulo $(X_0,X_1)^{q+2}$ (`hf`), and a ring isomorphism $e$ from the adic completion of the stalk at $z$ onto $S = \hat{A}[[X_0,X_1]]/(C(t)v - fu)$, where $t$ is viewed in $\hat A$. With $\mathrm{STK}$ the stalk at $z$, $\mathrm{CMP}$ its adic completion, $\mathrm{toC}$ the canonical map, $\mathrm{mkS}$ the quotient map onto $S$, and $\mathrm{germY}$ the canonical homomorphism from `chartAlgFin A K j` to $\mathrm{STK}$ (germ at $z$ on the open image of `ιFin A K j`), the theorem assumes: $\psi(\sigma_0 a) =$ the image of $a$ under $A_0 \to A \to \hat{A}$ for all $a \in A_0$; $\psi$ maps the maximal ideal of $W_0$ into that of $\hat{A}$; $f = \mathrm{MvPowerSeries.map}\,\psi\,f_0$; the compatibility of the two charts, namely that whenever $e_0$ sends the completed germ of a chart-algebra element $x$ over the cyclotomic side to the class of $s \in W_0[[X_0,X_1]]$, then $e(\mathrm{toC}(\mathrm{germY}(c\,x))) = \mathrm{mkS}(\mathrm{MvPowerSeries.map}\,\psi\,s)$; and the constants clause for $e$, namely that for every $a \in A$, $e$ carries the completed germ of $a$ along `toBase` to the class of $C(a)$ in $S$.
--
--   **Conclusion.** Under these hypotheses, for every $d \in (\mathbb{Z}/q)^\times$, every $\sigma_L \in \operatorname{Aut}(L)$ and $\sigma_A \in \operatorname{Aut}(A)$ with $\operatorname{algebraMap}(\sigma_A a) = \sigma_L(\operatorname{algebraMap} a)$ for all $a \in A$ and $\sigma_A(a) - a$ in the maximal ideal of $A$ for all $a$, for every $\pi \in A$ with $\pi^{q^2-1} = q$, every $\alpha t \in A$ with $\sigma_A(\pi) = \alpha t \cdot \pi$ and $\alpha t^{\,q+1} - (d : \mathbb{Z}/q).\mathrm{val}$ in the maximal ideal of $A$, and every ring automorphism $\tau$ of $K$ acting coefficientwise by $\sigma_L$ on Laurent expansions, the following hold.
--
--   First, $\tau$ maps `chartAlgFin A K j` into itself.
--
--   Secondly, for every proof `hpres` of that stability, with $\tau|$ the induced automorphism of the chart algebra:
--
--   (i) $\tau|(a) - a \in y.\mathrm{asIdeal}$ for every chart-algebra element $a$;
--
--   (ii) there exist a ring automorphism $\theta$ of $S$, a ring automorphism $\sigma_W$ of $\hat{A}$, an element $ct \in \hat{A}$ and a matrix $M \in \mathrm{Mat}_2(\hat{A})$ such that: $\theta(e(\mathrm{toC}(\mathrm{germY}(a)))) = e(\mathrm{toC}(\mathrm{germY}(\tau| a)))$ for every chart-algebra element $a$; $\sigma_W$ restricted along $A \to \hat{A}$ agrees with $\sigma_A$; $\sigma_W(w) - w$ lies in the maximal ideal of $\hat{A}$ for every $w$; $\theta(\mathrm{mkS}(C(w))) = \mathrm{mkS}(C(\sigma_W w))$ for every $w \in \hat{A}$; for each index $jj$, $\theta(\mathrm{mkS}(X_{jj})) - \mathrm{mkS}\big(\sum_{ii} C(M_{ii,jj})X_{ii}\big)$ lies in the square of the ideal generated by the classes of $X_0$ and $X_1$; $ct - \alpha t^{\,q+1}$ lies in the maximal ideal of $\hat{A}$; and for all indices $ii, jj$, $M_{ii,jj} - ct \cdot \big(\text{image in } \hat{A} \text{ of the natural-number representative of the } (ii,jj) \text{ entry of } \mathrm{diagOneElem}\,q\,(d^q)^{-1}\big)$ lies in the maximal ideal of $\hat{A}$.
--
--   Thus the linear part of the semilinear automorphism induced by $\tau$ on the Drinfeld chart is, modulo the maximal ideal, the scalar $\alpha t^{\,q+1}$ times the diagonal matrix $\mathrm{diag}(1,(d^q)^{-1})$, the scalar $d$ of the cyclotomic hypothesis being replaced by $ct$.
--
--   This is the base-change step in the construction of the Drinfeld local chart at a supersingular point of a modular curve of level $\Gamma_{H_1}(q^2M')$ with an auxiliary $\Gamma_1(\ell)$ guard condition at a prime $\ell \equiv 11 \pmod{12}$: the semilinear tame-inertia description of the completed local ring, established over cyclotomic constants, is carried along a comparison $A_0 \to A$ to a general discrete valuation base $A$ with algebraically closed residue field, the inertia parameter $d$ being read off from the action on a $(q^2-1)$-st root $\pi$ of $q$. It is used by [`ModularCurve.FullLevel.AuxLevelOne.exists_ringEquiv_adicCompletion_stalk_drinfeldChart_levelAut_linearPart_inertia_of_mem_ssJSet_of_pow_eq_mul_of_isPrimitiveRoot_mul_of_dvd`](thm.html#ModularCurve.FullLevel.AuxLevelOne.exists_ringEquiv_adicCompletion_stalk_drinfeldChart_levelAut_linearPart_inertia_of_mem_ssJSet_of_pow_eq_mul_of_isPrimitiveRoot_mul_of_dvd), which packages the existence of such a chart together with the inertia action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_inertia_drinfeldChart_baseChange_semilinear_linearPart_of_cyclotomicWitness_inertia_of_isAlgClosed_of_isPrimitiveRoot_mul_of_dvd.lean

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

theorem ModularCurve.FullLevel.AuxLevelOne.inertia_drinfeldChart_baseChange_semilinear_linearPart_of_cyclotomicWitness_inertia_of_isAlgClosed_of_isPrimitiveRoot_mul_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hζξ : ζ = ξ ^ ℓ)
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
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
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L₀ (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
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
    (hconst₀ :
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

      (∀ a : A₀, e₀ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
          (((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ ⊤ z₀ trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A₀ (↥K₀) j₀).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (σ₀ a))))
    (hinert₀ :
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

      (∀ (d : (ZMod q)ˣ) (σL : L₀ ≃+* L₀) (σA : A₀ ≃+* A₀),
        (∀ a : A₀, algebraMap A₀ L₀ (σA a) = σL (algebraMap A₀ L₀ a)) →

        (∀ a : A₀, σA a - a ∈ IsLocalRing.maximalIdeal A₀) →

        σL ζ₀ = ζ₀ ^ ((d : ZMod q).val) →
        ∀ τ : ↥K₀ ≃+* ↥K₀,

          (∀ x : ↥K₀, ((τ x : ↥K₀) : LaurentSeries L₀) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K₀) : LaurentSeries L₀)) →

          (∀ a : ↥K₀, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →
            τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) ∧
          ∀ hpres : (∀ a : ↥K₀, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)),

            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
              (((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) - a ∈ y₀.asIdeal)) ∧

            ∃ (θ : S₀ ≃+* S₀) (σW : W₀ ≃+* W₀) (M : Matrix (Fin 2) (Fin 2) W₀),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
                θ (e₀ (toC₀ (germY₀ a))) = e₀ (toC₀ (germY₀ ((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) hpres) a)))) ∧
              (∀ a : A₀, σW (σ₀ a) = σ₀ (σA a)) ∧
              (∀ w : W₀, σW w - w ∈ IsLocalRing.maximalIdeal W₀) ∧
              (∀ w : W₀, θ (mkS₀ (MvPowerSeries.C w)) = mkS₀ (MvPowerSeries.C (σW w))) ∧
              (∀ jj : Fin 2, θ (mkS₀ (MvPowerSeries.X jj)) -
                  mkS₀ (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                (Ideal.span {mkS₀ (MvPowerSeries.X 0), mkS₀ (MvPowerSeries.X 1)}) ^ 2) ∧
              (∀ ii jj : Fin 2, M ii jj -
                  ((((d : ZMod q) * ((ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹ : CuspidalType.GL2 q) :
                      Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val : ℕ) : W₀) ∈ IsLocalRing.maximalIdeal W₀)))

    (ψ : W₀ →+* (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (f u v : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q (AdicCompletion (IsLocalRing.maximalIdeal A) A) ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A)), MvPowerSeries.X 1}) ^ (q + 2))
    (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
      MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u}) :
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

      (∀ a : A₀, ψ (σ₀ a) = (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (algebraMap A₀ A a)) →
      (∀ w : W₀, w ∈ IsLocalRing.maximalIdeal W₀ → ψ w ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) →
      f = MvPowerSeries.map ψ f₀ →

      (∀ (x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) (s : MvPowerSeries (Fin 2) W₀),
        e₀ (algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
          ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)) x)) =
          Ideal.Quotient.mk _ s →
        e (toC (germY (c x))) = mkS (MvPowerSeries.map ψ s)) →

      (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) a))) →

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

          ∃ (θ : S ≃+* S) (σW : (AdicCompletion (IsLocalRing.maximalIdeal A) A) ≃+* (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (ct : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (M : Matrix (Fin 2) (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A)),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              θ (e (toC (germY a))) = e (toC (germY ((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧
            (∀ a : A, σW ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) a) = (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (σA a)) ∧
            (∀ w : (AdicCompletion (IsLocalRing.maximalIdeal A) A), σW w - w ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∧
            (∀ w : (AdicCompletion (IsLocalRing.maximalIdeal A) A), θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C (σW w))) ∧
            (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
              (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧

            (ct - (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (αt ^ (q + 1)) ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∧
            (∀ ii jj : Fin 2, M ii jj -
                ct * (((((ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹ : CuspidalType.GL2 q) :
                    Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val : ℕ) : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by sorry
