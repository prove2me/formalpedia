-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_inertia_drinfeldChart_semilinear_linearPart_diagOneElem_of_linearPart_riders_twoChartIntegralModel
-- name    : ModularCurve.FullLevel.AuxLevel.inertia_drinfeldChart_semilinear_linearPart_diagOneElem_of_linearPart_riders_twoChartIntegralModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/acefd5da-077c-59b2-a7a1-0e982d9545de
-- title:
--   Tame inertia on the Drinfeld chart: linear part d diag(1,d^{-q})
-- statement:
--   Fix a prime $q\ge 5$, a positive integer $M'$ with $q\nmid M'$, and a prime $\ell\ge 3$ with $\ell\ne q$ and $\ell\nmid M'$ (hypotheses `hq`, `hqM'`, `hℓ3`, `hℓq`, `hℓM'`). Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, let $\zeta\in L$ be a primitive $q$-th root of unity and $\xi\in L$ a primitive $q\ell$-th root of unity. Let $K$ be an intermediate field of $L\subseteq\mathrm{LaurentSeries}\,L$ which by `hK` equals [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField ((q*ℓ)^2*M') (ModularCurve.FullLevel.levelH (q*ℓ) M'))`](def/ModularCurve_LaurentCoeff.html#L103): the field generated over $L$ inside $L((t))$ by the coefficientwise image of the $q$-expansion function field of $X_H$ of level $(q\ell)^2M'$, where $H=$ `levelH (q*ℓ) M'` is the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$.
--
--   Let $A$ be a discrete valuation domain with fraction field $L$, lying above $q$ in the sense that $q\in\mathfrak{m}_A$ (`hAq`), with $\zeta$ in the image of $A$ (`hζA`), and with $K$ an $A$-algebra compatibly with the tower $A\subseteq L\subseteq K$. Let $j\in K$ be the element whose Laurent series is the coefficientwise image [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion of the $j$-function (`hj`), assumed nonzero, and let $\varpi$ generate $\mathfrak{m}_A$ (`hϖ`).
--
--   Consider the scheme $X=$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), the pushout gluing $\operatorname{Spec}$ of the chart algebra `chartAlgFin A K j` of elements of $K$ integral over $A[j]$ to $\operatorname{Spec}$ of the chart algebra `chartAlgInf A K j` of elements integral over $A[j^{-1}]$ along the middle chart, together with its structure morphism `toBase` to $\operatorname{Spec}A$. Let $z$ be a point of $X$ and let $\varpi_z$ be the germ at $z$ of the global image of $\varpi$ under `toBase` (`hϖz`), assumed to lie in the maximal ideal of the stalk $\mathrm{STK}=\mathcal{O}_{X,z}$ (`hz`), so that $z$ lies in the fibre over the closed point of $\operatorname{Spec}A$. Let $y$ be a point of $\operatorname{Spec}$ `chartAlgFin A K j` mapping to $z$ under `ιFin` (`hy`). The supersingularity hypothesis `hss` requires: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from the chart algebra to $\Omega$ with kernel $y.\mathrm{asIdeal}$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), that is, every elliptic curve over $\Omega$ with that $j$-invariant has no nonzero point killed by $q$.
--
--   Let $W$ be a complete discrete valuation domain and $\sigma:A\to W$ a ring homomorphism with $\mathfrak{m}_W=(\sigma\varpi)$ (`hσϖ`). Let $f,u,v\in W[[X_0,X_1]]$ with $u,v$ units (`hu`, `hv`) and $f$ congruent to the Drinfeld form [`DrinfeldCurve.LocalChart.drinfeldForm q W`](def/DrinfeldCurve_LocalChart.html#L18) $=X_0X_1^q-X_0^qX_1$ modulo $(X_0,X_1)^{q+2}$ (`hf`). Put $S=W[[X_0,X_1]]/(C(\sigma\varpi)v-fu)$, write $\mathrm{mkS}$ for the quotient map, and let $e$ be a ring isomorphism from the $\mathfrak{m}$-adic completion $\mathrm{CMP}$ of $\mathrm{STK}$ onto $S$. Write $\mathrm{toC}:\mathrm{STK}\to\mathrm{CMP}$ for the completion map and $\mathrm{germY}$ for the homomorphism from the chart algebra to $\mathrm{STK}$ obtained from the identification of the sections of $X$ over the image of `ιFin` with the chart algebra followed by the germ at $z$.
--
--   Three hypotheses on this chart witness are imposed.
--
--   (`hconst`, constants) For every $a\in A$, the element $e(\mathrm{toC}(\text{germ of }a\text{ via }\mathrm{toBase}))$ equals $\mathrm{mkS}(C(\sigma a))$.
--
--   (`hlin`, equivariant linear parts) For every $\gamma\in\mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M')$ and every $L$-algebra automorphism $\tau$ of $K$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt L (q*ℓ) ξ (q*ℓ) ((q*ℓ)^2*M') (levelH (q*ℓ) M') γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29) — i.e. on every element $x\in K$ whose Laurent series is the coefficientwise image of a ratio $p_f/p_g$ of integral $q$-expansions of modular forms of weight $k$ for $\Gamma_H$ of level $(q\ell)^2M'$, and for every embedding $\iota:L\to\mathbb{C}$ with $\iota\xi=e^{2\pi i/(q\ell)}$, the coefficientwise image $\iota(\tau x)$ times the $q$-expansion of $g\mid_k$ `conjElemN (q*ℓ) γ⁻¹` equals the $q$-expansion of $f\mid_k$ `conjElemN (q*ℓ) γ⁻¹` — and for every proof that $\tau$ maps the chart algebra `chartAlgFin A K j` into itself, if the induced endomorphism of the chart algebra satisfies $\tau(a)-a\in y.\mathrm{asIdeal}$ for all $a$, then there are a ring automorphism $\theta$ of $S$, an element $c\in W$ and a matrix $M\in M_2(W)$ such that: $\theta\circ e\circ\mathrm{toC}\circ\mathrm{germY}=e\circ\mathrm{toC}\circ\mathrm{germY}\circ\tau$ on the chart algebra; $\theta$ fixes $\mathrm{mkS}(C w)$ for every $w\in W$; for each index $jj$ the difference $\theta(\mathrm{mkS}(X_{jj}))-\mathrm{mkS}\bigl(\sum_{ii}C(M_{ii\,jj})X_{ii}\bigr)$ lies in $(\mathrm{mkS}(X_0),\mathrm{mkS}(X_1))^2$; $c^{q+1}-1\in\mathfrak{m}_W$; $M_{ii\,jj}\equiv c\,\gamma_{ii\,jj}$ modulo $\mathfrak{m}_W$ for all $ii,jj$; if $\gamma\in\Gamma(\ell)$ then $c\equiv 1$ modulo $\mathfrak{m}_W$; and if $\gamma\in\Gamma(q)$ and $\tau$ is not the identity on $K$ then $c-1\notin\mathfrak{m}_W$.
--
--   (`hanchor`, anchored branch) For every prime ideal $P$ of $S$ with $\mathrm{mkS}(X_0)\notin P$ or $\mathrm{mkS}(X_1)\notin P$, containing $\mathrm{mkS}(C(\sigma\varpi))$, and containing an element $\mathrm{mkS}(C(1)X_0+C(0)X_1+h)$ for some $h\in(X_0,X_1)^2$, and for every $a$ in the chart algebra: $\mathrm{toC}(\mathrm{germY}\,a)$ lies in the preimage of $P$ under $e$ if and only if every Laurent coefficient $\mathrm{coeff}_n(a)$, $n\in\mathbb{Z}$, is the image under $A\to L$ of an element of $\mathfrak{m}_A$.
--
--   Under these hypotheses the following holds. Let $d\in(\mathbb{Z}/q)^\times$, let $\sigma_L$ be a ring automorphism of $L$ and $\sigma_A$ a ring automorphism of $A$ such that $\sigma_L$ restricts to $\sigma_A$ along $A\to L$, such that $\sigma_A a-a\in\mathfrak{m}_A$ for all $a\in A$, and such that $\sigma_L\zeta=\zeta^{\,d.\mathrm{val}}$. Let $\tau$ be a ring automorphism of $K$ acting coefficientwise by $\sigma_L$, that is, the Laurent series of $\tau x$ is [`ModularCurve.coeffMap σL.toRingHom`](def/ModularCurve_LaurentCoeff.html#L16) applied to the Laurent series of $x$, for every $x\in K$. Then:
--
--   first, $\tau$ maps `chartAlgFin A K j` into itself; and second, for every proof $hpres$ of this preservation, both of the following hold.
--
--   (a) For every $a$ in the chart algebra, the induced endomorphism satisfies $\tau(a)-a\in y.\mathrm{asIdeal}$.
--
--   (b) There exist a ring automorphism $\theta$ of $S$, a ring automorphism $\sigma_W$ of $W$ and a matrix $M\in M_2(W)$ such that:
--
--   • $\theta(e(\mathrm{toC}(\mathrm{germY}\,a)))=e(\mathrm{toC}(\mathrm{germY}(\tau a)))$ for every $a$ in the chart algebra;
--
--   • $\sigma_W(\sigma a)=\sigma(\sigma_A a)$ for every $a\in A$;
--
--   • $\sigma_W w-w\in\mathfrak{m}_W$ for every $w\in W$;
--
--   • $\theta(\mathrm{mkS}(C w))=\mathrm{mkS}(C(\sigma_W w))$ for every $w\in W$, so $\theta$ is $\sigma_W$-semilinear on constants;
--
--   • for each index $jj$, $\theta(\mathrm{mkS}(X_{jj}))-\mathrm{mkS}\bigl(\sum_{ii}C(M_{ii\,jj})X_{ii}\bigr)\in(\mathrm{mkS}(X_0),\mathrm{mkS}(X_1))^2$;
--
--   • for all $ii,jj$, $M_{ii\,jj}-\bigl(\bigl((d\cdot\mathrm{diagOneElem}\,q\,(d^q)^{-1})_{ii\,jj}\bigr).\mathrm{val}\bigr)\in\mathfrak{m}_W$, where [`ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹`](def/ModularCurve_FullLevelJacobian.html#L233) is the element $\mathrm{diag}(1,(d^q)^{-1})$ of $\mathrm{GL}_2(\mathbb{Z}/q)$, its matrix is scaled by $d\in\mathbb{Z}/q$, and entries of $\mathbb{Z}/q$ are lifted to $W$ through their natural-number representatives. Thus the linear part of $\theta$ is, modulo $\mathfrak{m}_W$, the reduction of $d\cdot\mathrm{diag}(1,d^{-q})$.
--
--   This is the inertia law on the Drinfeld-type local chart at a supersingular point of the two-chart integral model of the level-$(q\ell)^2M'$ modular curve over a discrete valuation ring above $q$: an automorphism of the function field acting coefficientwise by a field automorphism that is trivial modulo $\mathfrak{m}_A$ and sends $\zeta\mapsto\zeta^d$ induces a $\sigma_W$-semilinear automorphism of the formal chart whose linear part is $d\cdot\mathrm{diag}(1,d^{-q})$ modulo the maximal ideal. It is used by [`ModularCurve.FullLevel.AuxLevel.exists_ringEquiv_adicCompletion_stalk_drinfeldChart_of_levelAut_riders_inertia_of_mem_ssJSet_twoChartIntegralModel`](thm.html#ModularCurve.FullLevel.AuxLevel.exists_ringEquiv_adicCompletion_stalk_drinfeldChart_of_levelAut_riders_inertia_of_mem_ssJSet_twoChartIntegralModel), which packages the level-automorphism and inertia actions on the completed stalk into a single chart statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_inertia_drinfeldChart_semilinear_linearPart_diagOneElem_of_linearPart_riders_twoChartIntegralModel.lean

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

theorem ModularCurve.FullLevel.AuxLevel.inertia_drinfeldChart_semilinear_linearPart_diagOneElem_of_linearPart_riders_twoChartIntegralModel
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

      (∀ (d : (ZMod q)ˣ) (σL : L ≃+* L) (σA : A ≃+* A),
        (∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a)) →

        (∀ a : A, σA a - a ∈ IsLocalRing.maximalIdeal A) →

        σL ζ = ζ ^ ((d : ZMod q).val) →
        ∀ τ : ↥K ≃+* ↥K,

          (∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L)) →

          (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
            τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),

            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal)) ∧

            ∃ (θ : S ≃+* S) (σW : W ≃+* W) (M : Matrix (Fin 2) (Fin 2) W),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                θ (e (toC (germY a))) = e (toC (germY ((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧
              (∀ a : A, σW (σ a) = σ (σA a)) ∧
              (∀ w : W, σW w - w ∈ IsLocalRing.maximalIdeal W) ∧
              (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C (σW w))) ∧
              (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                  mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
              (∀ ii jj : Fin 2, M ii jj -
                  ((((d : ZMod q) * ((ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹ : CuspidalType.GL2 q) :
                      Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val : ℕ) : W) ∈ IsLocalRing.maximalIdeal W)) := by sorry
