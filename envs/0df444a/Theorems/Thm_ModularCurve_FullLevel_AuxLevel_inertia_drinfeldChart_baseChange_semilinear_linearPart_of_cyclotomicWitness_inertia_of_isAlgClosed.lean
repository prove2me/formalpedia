-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_inertia_drinfeldChart_baseChange_semilinear_linearPart_of_cyclotomicWitness_inertia_of_isAlgClosed
-- name    : ModularCurve.FullLevel.AuxLevel.inertia_drinfeldChart_baseChange_semilinear_linearPart_of_cyclotomicWitness_inertia_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/b5c90924-620d-579e-91ab-98a3699596f9
-- title:
--   Base change of the Drinfeld-chart tame inertia law
-- statement:
--   Throughout, $q$ is a prime with $5 \le q$, $M'$ a nonzero natural number with $q \nmid M'$, and $\ell$ a prime with $3 \le \ell$, $\ell \ne q$ and $\ell \nmid M'$.
--
--   **General constants.** $L$ is a field of characteristic zero carrying a primitive $q$-th root of unity $\zeta$ and a primitive $(q\ell)$-th root of unity $\xi$, and the hypothesis `hι` asks for a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\xi) = \exp(2\pi i/(q\ell))$. The field $K$ is an intermediate field of $L \subseteq$ `LaurentSeries L` required by `hK` to be [`ModularCurve.laurentBaseChange L`](def/ModularCurve_LaurentCoeff.html#L103) of [`ModularCurve.xHFunctionField ((q*ℓ)^2*M') (ModularCurve.FullLevel.levelH (q*ℓ) M')`](def/ModularCurve_XH.html#L79); that is, $K$ is generated over $L$, inside the Laurent series field of $L$, by the coefficientwise image of the field of $q$-expansions over $\mathbb{Q}$ of the modular curve $X_H$ of level $(q\ell)^2M'$, where $H = \ker\big((\mathbb{Z}/(q\ell)^2M')^\times \to (\mathbb{Z}/q\ell)^\times\big)$ is the group of units congruent to $1$ modulo $q\ell$. Next, $A$ is a discrete valuation domain with fraction field $L$ whose residue field is algebraically closed, with $q \in \mathfrak m_A$ and $\zeta$ in the image of $A \to L$, and $A$ acts on $K$ compatibly with $A \to L \subseteq K$. The element $j \in K$ is nonzero and its Laurent expansion is the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), the $q$-expansion of the modular function $j$. The element $\varpi$ generates $\mathfrak m_A$, and $t \in A$ satisfies $t^{q-1} = q\,w$ for some unit $w$ of $A$ (hypothesis `ht`).
--
--   The scheme [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) is the pushout gluing $\operatorname{Spec}$ of `chartAlgFin A K j`, the subalgebra of elements of $K$ integral over $A[j]$, to $\operatorname{Spec}$ of `chartAlgInf A K j` (elements integral over $A[j^{-1}]$) along the middle chart; `toBase` is its structure morphism to $\operatorname{Spec} A$ and `ιFin` the morphism from the finite chart $\mathrm{XFin} = \operatorname{Spec}($`chartAlgFin`$)$. A point $z$ of this model is given, together with the element $\varpi z$ of the stalk at $z$, which `hϖz` identifies with the germ at $z$ of the pullback of $\varpi$ along `toBase`, and `hz` requires $\varpi z$ to lie in the maximal ideal of that stalk. A point $y$ of $\mathrm{XFin}$ with `ιFin` $(y) = z$ is given (`hy`), and the hypothesis `hss` requires: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from `chartAlgFin A K j` to $\Omega$ with kernel $y.\mathrm{asIdeal}$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), i.e. every elliptic curve over $\Omega$ with that $j$-invariant has no point $P \neq 0$ with $q \cdot P = 0$.
--
--   **Cyclotomic constants.** The same package is given over a field $L_0$ of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $\{q\ell\}$: roots of unity $\zeta_0$ (primitive of order $q$) and $\xi_0$ (primitive of order $q\ell$); an intermediate field $K_0$ of $L_0 \subseteq$ `LaurentSeries L₀` equal to the same Laurent base change, now over $L_0$; a discrete valuation domain $A_0$ with fraction field $L_0$, with $q \in \mathfrak m_{A_0}$ and $\zeta_0$ in the image of $A_0$, acting on $K_0$ compatibly; a nonzero $j_0 \in K_0$ with the same $q$-expansion; a generator $\varpi_0$ of $\mathfrak m_{A_0}$; a point $z_0$ of `TwoChartIntegralModel A₀ K₀ j₀` with the germ $\varpi z_0$ of $\varpi_0$ in the maximal ideal of the stalk; a point $y_0$ of the finite chart above $z_0$; and the supersingularity hypothesis `hss₀` for $y_0$ exactly as above. No hypothesis on the residue field of $A_0$ and no analogue of $t$ are imposed on this side.
--
--   **Comparison data.** A ring homomorphism $i : L_0 \to L$ with $i(\zeta_0) = \zeta$ and $i(\xi_0) = \xi$; an $A_0$-algebra structure on $A$ whose structure map is local and injective and satisfies $\mathrm{alg}_{A\to L}(\mathrm{alg}_{A_0 \to A}(a)) = i(\mathrm{alg}_{A_0 \to L_0}(a))$; the hypothesis `hϖ₀t` that the image of $\varpi_0$ in $A$ is $t$ times a unit; a ring homomorphism $c_K : K_0 \to K$ acting on Laurent expansions by applying $i$ coefficientwise, with $c_K(j_0) = j$; a ring homomorphism $c$ from `chartAlgFin A₀ K₀ j₀` to `chartAlgFin A K j` induced by $c_K$ (hypothesis `hc`), with $y.\mathrm{asIdeal}$ pulling back along $c$ to $y_0.\mathrm{asIdeal}$; and a ring isomorphism $\beta : A \otimes_{A_0}$ `chartAlgFin A₀ K₀ j₀` $\cong$ `chartAlgFin A K j` with $\beta(a \otimes b)$ equal to the image of $a$ times $c(b)$.
--
--   **The cyclotomic chart witness.** $W_0$ is a discrete valuation domain, complete for its maximal-ideal adic topology, $\sigma_0 : A_0 \to W_0$ a ring homomorphism with $\mathfrak m_{W_0} = (\sigma_0 \varpi_0)$; $f_0, u_0, v_0 \in W_0[[X_0,X_1]]$ with $u_0, v_0$ units and $f_0 - (X_0X_1^q - X_0^qX_1) \in (X_0,X_1)^{q+2}$ (the Drinfeld form [`DrinfeldCurve.LocalChart.drinfeldForm q W₀`](def/DrinfeldCurve_LocalChart.html#L18)); and $e_0$ is a ring isomorphism from the $\mathfrak m$-adic completion of the stalk at $z_0$ onto $S_0 := W_0[[X_0,X_1]]/\big(C(\sigma_0\varpi_0)v_0 - f_0u_0\big)$. Write $\mathrm{toC}_0$ for the map from the stalk to its completion, $\mathrm{mk}_{S_0}$ for the quotient map and $\mathrm{germY}_0$ for the homomorphism from `chartAlgFin A₀ K₀ j₀` to the stalk at $z_0$ obtained from the germ along the open image of `ιFin`. The hypothesis `hconst₀` states that for every $a \in A_0$, $e_0$ carries the image in the completed stalk of the germ of $a$ (via `toBase`) to the class of $C(\sigma_0 a)$.
--
--   The hypothesis `hinert₀` is the cyclotomic tame-inertia clause: for every $d \in (\mathbb{Z}/q)^\times$, every pair of ring automorphisms $\sigma_L$ of $L_0$ and $\sigma_A$ of $A_0$ with $\mathrm{alg}_{A_0\to L_0}(\sigma_A a) = \sigma_L(\mathrm{alg}_{A_0\to L_0} a)$ for all $a$, with $\sigma_A a - a \in \mathfrak m_{A_0}$ for all $a$, and with $\sigma_L \zeta_0 = \zeta_0^{\,\mathrm{val}(d)}$, and every ring automorphism $\tau$ of $K_0$ acting on Laurent expansions by applying $\sigma_L$ coefficientwise: first, $\tau$ maps `chartAlgFin A₀ K₀ j₀` into itself; and second, for every proof `hpres` of this preservation, the restriction $\tau|$ of $\tau$ to that algebra satisfies $\tau|(a) - a \in y_0.\mathrm{asIdeal}$ for all $a$, and there exist a ring automorphism $\theta$ of $S_0$, a ring automorphism $\sigma_W$ of $W_0$ and a matrix $M \in M_2(W_0)$ such that: $\theta(e_0(\mathrm{toC}_0(\mathrm{germY}_0 a))) = e_0(\mathrm{toC}_0(\mathrm{germY}_0(\tau| a)))$ for all $a$; $\sigma_W \circ \sigma_0 = \sigma_0 \circ \sigma_A$; $\sigma_W w - w \in \mathfrak m_{W_0}$ for all $w$; $\theta$ sends the class of $C(w)$ to the class of $C(\sigma_W w)$; for each index $jj$ the difference $\theta(X_{jj}) - \sum_{ii} C(M_{ii\,jj})X_{ii}$ lies in the square of the ideal generated by the classes of $X_0, X_1$; and entrywise $M_{ii\,jj} \equiv \big((d)\cdot \mathrm{diag}(1,(d^q)^{-1})\big)_{ii\,jj} \bmod \mathfrak m_{W_0}$, the matrix being [`ModularCurve.FullLevel.diagOneElem q (d^q)⁻¹`](def/ModularCurve_FullLevelJacobian.html#L233) in $\mathrm{GL}_2(\mathbb{Z}/q)$ scaled by $d$ and lifted to $W_0$ through the natural-number values of its entries.
--
--   **The base-changed witness.** Let $\hat A$ denote the $\mathfrak m_A$-adic completion of $A$. There are given a ring homomorphism $\psi : W_0 \to \hat A$; elements $f, u, v \in \hat A[[X_0,X_1]]$ with $u, v$ units and $f - (X_0X_1^q - X_0^qX_1) \in (X_0,X_1)^{q+2}$; and a ring isomorphism $e$ from the $\mathfrak m$-adic completion of the stalk at $z$ onto $S := \hat A[[X_0,X_1]]/\big(C(\hat t)v - fu\big)$, where $\hat t$ is the image of $t$ in $\hat A$. Write $\mathrm{toC}$, $\mathrm{mk}_S$ and $\mathrm{germY}$ for the corresponding maps on the general side. Five further hypotheses are assumed, as antecedents of the conclusion: (i) $\psi(\sigma_0 a)$ equals the image in $\hat A$ of $\mathrm{alg}_{A_0 \to A}(a)$ for all $a \in A_0$; (ii) $\psi$ carries $\mathfrak m_{W_0}$ into $\mathfrak m_{\hat A}$; (iii) $f$ is the coefficientwise image of $f_0$ under $\psi$; (iv) for every $x$ in `chartAlgFin A₀ K₀ j₀` and every $s \in W_0[[X_0,X_1]]$, if $e_0$ sends the image in the completed stalk of $\mathrm{germY}_0(x)$ to the class of $s$, then $e(\mathrm{toC}(\mathrm{germY}(c\,x))) = \mathrm{mk}_S(\psi_*s)$; (v) for every $a \in A$, $e$ sends the image in the completed stalk of the germ of $a$ (via `toBase`) to the class of $C$ of the image of $a$ in $\hat A$.
--
--   **Conclusion.** For every $d \in (\mathbb{Z}/q)^\times$, every ring automorphism $\sigma_L$ of $L$ and every ring automorphism $\sigma_A$ of $A$ such that $\mathrm{alg}_{A\to L}(\sigma_A a) = \sigma_L(\mathrm{alg}_{A\to L} a)$ for all $a \in A$ and $\sigma_A a - a \in \mathfrak m_A$ for all $a \in A$; for every $\pi \in A$ with $\pi^{q^2-1} = q$ and every $\tilde\alpha \in A$ with $\sigma_A \pi = \tilde\alpha\,\pi$ and $\tilde\alpha^{\,q+1} - \mathrm{val}(d) \in \mathfrak m_A$; and for every ring automorphism $\tau$ of $K$ acting on Laurent expansions by applying $\sigma_L$ coefficientwise, the following hold.
--
--   First, $\tau$ maps `chartAlgFin A K j` into itself. Secondly, for every proof `hpres` of this preservation, writing $\tau|$ for the induced endomorphism of that algebra:
--
--   (1) $\tau|(a) - a \in y.\mathrm{asIdeal}$ for every $a$ in `chartAlgFin A K j`;
--
--   (2) there exist a ring automorphism $\theta$ of $S$, a ring automorphism $\sigma_W$ of $\hat A$, an element $c_t \in \hat A$ and a matrix $M \in M_2(\hat A)$ such that
--
--   (2a) $\theta(e(\mathrm{toC}(\mathrm{germY}\,a))) = e(\mathrm{toC}(\mathrm{germY}(\tau| a)))$ for all $a$ in `chartAlgFin A K j`;
--
--   (2b) $\sigma_W$ of the image of $a$ in $\hat A$ is the image of $\sigma_A a$, for all $a \in A$;
--
--   (2c) $\sigma_W w - w \in \mathfrak m_{\hat A}$ for all $w \in \hat A$;
--
--   (2d) $\theta(\mathrm{mk}_S(C(w))) = \mathrm{mk}_S(C(\sigma_W w))$ for all $w \in \hat A$;
--
--   (2e) for each index $jj$, $\theta(\mathrm{mk}_S(X_{jj})) - \mathrm{mk}_S\big(\sum_{ii} C(M_{ii\,jj})X_{ii}\big)$ lies in the square of the ideal of $S$ generated by the classes of $X_0$ and $X_1$;
--
--   (2f) $c_t$ minus the image of $\tilde\alpha^{\,q+1}$ in $\hat A$ lies in $\mathfrak m_{\hat A}$;
--
--   (2g) for all indices $ii, jj$, $M_{ii\,jj} - c_t \cdot \big(\mathrm{diag}(1,(d^q)^{-1})\big)_{ii\,jj} \in \mathfrak m_{\hat A}$, the matrix being [`ModularCurve.FullLevel.diagOneElem q (d^q)⁻¹`](def/ModularCurve_FullLevelJacobian.html#L233) in $\mathrm{GL}_2(\mathbb{Z}/q)$ with entries lifted to $\hat A$ through their natural-number values.
--
--   Thus on the general side the scalar $d$ of the cyclotomic linear-part congruence is replaced by a constant $c_t$ congruent to $\tilde\alpha^{\,q+1}$ modulo $\mathfrak m_{\hat A}$, and the hypothesis $\sigma_L \zeta_0 = \zeta_0^{\mathrm{val}(d)}$ is replaced by the existence of $\pi$ with $\pi^{q^2-1} = q$, $\sigma_A\pi = \tilde\alpha\pi$ and $\tilde\alpha^{\,q+1} \equiv \mathrm{val}(d)$.
--
--   This is the base-change step in the description of the tame inertia action on the completed local ring at a supersingular point of a two-chart integral model of the modular curve of level $(q\ell)^2M'$ with $H$ the units congruent to $1$ modulo $q\ell$: a Drinfeld local chart $W_0[[X_0,X_1]]/(\varpi_0 v_0 - f_0u_0)$ together with its inertia law over cyclotomic constants is transported, along a flat comparison $A \otimes_{A_0} \mathrm{chartAlgFin}_0 \cong \mathrm{chartAlgFin}$, to a chart over the completion of an arbitrary discrete valuation ring $A$ with algebraically closed residue field, the cyclotomic character value $d$ being read off from $\sigma_A\pi = \tilde\alpha\pi$ for a $(q^2-1)$-st root $\pi$ of $q$. It is cited by [`ModularCurve.FullLevel.AuxLevel.exists_ringEquiv_adicCompletion_stalk_drinfeldChart_levelAut_linearPart_inertia_of_mem_ssJSet_of_pow_eq_mul_of_isAlgClosed`](thm.html#ModularCurve.FullLevel.AuxLevel.exists_ringEquiv_adicCompletion_stalk_drinfeldChart_levelAut_linearPart_inertia_of_mem_ssJSet_of_pow_eq_mul_of_isAlgClosed), which produces such a chart together with its inertia law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_inertia_drinfeldChart_baseChange_semilinear_linearPart_of_cyclotomicWitness_inertia_of_isAlgClosed.lean

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

theorem ModularCurve.FullLevel.AuxLevel.inertia_drinfeldChart_baseChange_semilinear_linearPart_of_cyclotomicWitness_inertia_of_isAlgClosed
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
