-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_formallySmooth_fiber_maximalIdeal_blowupChart_of_drinfeldChartWitness
-- name    : ModularCurve.FullLevel.AuxLevel.formallySmooth_fiber_maximalIdeal_blowupChart_of_drinfeldChartWitness
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/d0093e43-3a35-5445-85c3-1d8139f6fff8
-- title:
--   Formal smoothness of the special fibre of the blow-up chart
-- statement:
--   **Arithmetic data.** Let $q\ge 5$ be a prime, $M'$ a nonzero natural number with $q\nmid M'$, and $\ell\ge 3$ a prime with $\ell\ne q$ and $\ell\nmid M'$. Let $L$ be a field of characteristic $0$ and $\xi\in L$ a primitive $(q\ell)$-th root of unity; the hypothesis `hι` requires the existence of a ring homomorphism $\iota:L\to\mathbb{C}$ with $\iota(\xi)=e^{2\pi i/(q\ell)}$.
--
--   **The function field.** Let $K$ be an intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ which, by `hK`, is [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField ((q*ℓ)^2*M') (ModularCurve.FullLevel.levelH (q*ℓ) M'))`](def/ModularCurve_LaurentCoeff.html#L103): the subfield of $\mathrm{LaurentSeries}\,L$ generated over $L$ by the coefficientwise images, under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81), of the rational $q$-expansion function field of the congruence subgroup $\Gamma_H\le \mathrm{SL}_2(\mathbb{Z})$ of level $N_0=(q\ell)^2M'$ attached to $H=\ker\bigl((\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times\bigr)$, the group of units congruent to $1$ modulo $q\ell$.
--
--   **The base ring.** Let $A$ be a discrete valuation ring which is a domain, equipped with an $L$-algebra structure making $L$ its fraction field, Henselian local with algebraically closed residue field, such that $q\in\mathfrak{m}_A$ (`hAq`) and $\xi$ lies in the image of $A\to L$ (`hξA`); $K$ is an $A$-algebra compatibly with $L$. Let $j\in K$ be nonzero whose underlying Laurent series is [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), the coefficientwise image of the rational $q$-expansion $q^{-1}\cdot j_{\mathrm{num}}$ of the modular invariant (`hj`). Let $\varpi\in A$ generate $\mathfrak m_A$ (`hϖ`), and let $\varpi_t\in A$ satisfy $\varpi_t^{\,q^2-1}=q\,u$ for some unit $u$ (`hϖt`), so that $\varpi_t$ is a $(q^2-1)$-st root of $q$ up to a unit.
--
--   Throughout, $C:=$ `chartAlgFin A K j` denotes the $j$-finite chart algebra, i.e. the $A$-subalgebra of elements of $K$ integral over $A[j]$, and $X_{\mathrm{fin}}=\operatorname{Spec} C$.
--
--   **The supersingular point.** Let $y\subseteq C$ be a maximal ideal containing the image of $\varpi$ (`hy`, `hϖy`), subject to the supersingularity condition `hss`: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi:C\to\Omega$ with kernel $y$, the element $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), that is, every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $\varphi(j)$ has no nonzero affine point killed by $q$.
--
--   **The point of the two-chart model.** Let $z$ be a point of the scheme [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) (the pushout of $\operatorname{Spec}$ of the two chart algebras along the middle chart), let $\varpi_z$ be the germ at $z$ of the image of $\varpi$ under the structure morphism to $\operatorname{Spec} A$ (`hϖz`), and assume $\varpi_z$ lies in the maximal ideal of the stalk at $z$ (`hz`). Let $y'$ be a point of $X_{\mathrm{fin}}$ mapping to $z$ under `ιFin` (`hy'`), satisfying the same supersingularity condition `hss'` for its ideal, and with $y'.\mathrm{asIdeal}=y$ (`hy'y`).
--
--   **The Drinfeld chart presentation.** Let $W_1$ be a discrete valuation ring which is a domain, complete for the adic topology of its maximal ideal, let $\sigma_1:A\to W_1$ be a ring homomorphism with $\mathfrak m_{W_1}=(\sigma_1\varpi)$ (`hσ₁`), and let $f_1,u_1,v_1\in W_1[[X_0,X_1]]$ with $u_1,v_1$ units and $f_1\equiv X_0X_1^q-X_0^qX_1$ (the form [`DrinfeldCurve.LocalChart.drinfeldForm q W₁`](def/DrinfeldCurve_LocalChart.html#L18)) modulo $(X_0,X_1)^{q+2}$ (`hf₁`). Let
--   $$e_1:\widehat{\mathcal O}_{z}\;\xrightarrow{\ \sim\ }\;S:=W_1[[X_0,X_1]]/\bigl(C(\sigma_1(\varpi_t^{\,q+1}))v_1-f_1u_1\bigr)$$
--   be a ring isomorphism from the $\mathfrak m$-adic completion of the stalk at $z$ onto $S$. Write $\mathrm{toC}$ for the map from the stalk to its completion, $\mathrm{mk}_S$ for the quotient map onto $S$, and $\mathrm{germ}_Y:C\to\mathcal O_z$ for the germ map at $z$ obtained from the affine chart $\iota_{\mathrm{fin}}$.
--
--   The hypothesis `hW₁` is a conjunction of seven clauses:
--
--   1. $e_1$ is compatible with constants: for every $a\in A$, the image of the germ at $z$ of $a$ in the completion is sent by $e_1$ to $\mathrm{mk}_S(C(\sigma_1 a))$.
--
--   2. For every $\gamma\in\Gamma_0(M')$ and every $L$-algebra automorphism $\tau$ of $K$ which is a level automorphism at $\gamma^{-1}$ in the sense of [`ModularCurve.FullLevel.IsLevelAutAt L (q*ℓ) ξ (q*ℓ) ((q*ℓ)^2*M') (levelH (q*ℓ) M') γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29) (for all weights $k$ and modular forms $f,g$ of level $\Gamma_H(N_0)$ with integral $q$-expansions and $g\ne 0$, and every $x\in K$ whose Laurent series is the coefficientwise image of the quotient of those $q$-expansions, and every embedding $\iota$ with $\iota(\xi)=e^{2\pi i/(q\ell)}$, the image of $\tau(x)$ under $\iota$ multiplied by the $q$-expansion of $g\mid_k \mathrm{conjElemN}\,(q\ell)\,\gamma^{-1}$ equals the $q$-expansion of $f\mid_k \mathrm{conjElemN}\,(q\ell)\,\gamma^{-1}$), the automorphism $\tau$ maps $C$ into $C$.
--
--   3. For $\gamma\in\Gamma_0(M')\cap\Gamma(\ell)$, every level automorphism $\tau$ at $\gamma^{-1}$ preserving $C$ acts trivially modulo $y'$: $\tau(a)-a\in y'.\mathrm{asIdeal}$ for all $a\in C$.
--
--   4. For every $\gamma\in\Gamma_0(M')$, every level automorphism $\tau$ at $\gamma^{-1}$ preserving $C$ and acting trivially modulo $y'$ in the above sense, there exist a ring automorphism $\theta$ of $S$, an element $c\in W_1$ and a matrix $M\in M_2(W_1)$ such that: $\theta$ intertwines the $\tau$-action with the embedding $C\to S$, i.e. $\theta(e_1(\mathrm{toC}(\mathrm{germ}_Y a)))=e_1(\mathrm{toC}(\mathrm{germ}_Y(\tau a)))$ for all $a\in C$; $\theta$ fixes every constant $\mathrm{mk}_S(C(w))$, $w\in W_1$; for each coordinate $j_0$, $\theta(\mathrm{mk}_S(X_{j_0}))-\mathrm{mk}_S\bigl(\sum_i C(M_{i j_0})X_i\bigr)$ lies in the square of the ideal generated by $\mathrm{mk}_S(X_0),\mathrm{mk}_S(X_1)$; $c^{q+1}\equiv 1$ modulo $\mathfrak m_{W_1}$; $M_{ij}\equiv c\,\gamma_{ij}$ modulo $\mathfrak m_{W_1}$ for all $i,j$; if $\gamma\in\Gamma(\ell)$ then $c\equiv1$ modulo $\mathfrak m_{W_1}$; and if $\gamma\in\Gamma(q)$ and $\tau$ is not the identity on $K$ then $c\not\equiv1$ modulo $\mathfrak m_{W_1}$.
--
--   5. A separation clause for branches: for all integers $a_1,b_1,a_2,b_2$ and all prime ideals $P_1,P_2$ of $S$ such that each $P_i$ omits at least one of $\mathrm{mk}_S(X_0),\mathrm{mk}_S(X_1)$, each contains $\mathrm{mk}_S(C(\sigma_1\varpi))$, each contains an element $\mathrm{mk}_S\bigl(C(a_i)X_0+C(b_i)X_1+h\bigr)$ with $h\in(X_0,X_1)^2$, and $q\nmid a_1b_2-a_2b_1$, the contractions of $P_1$ and $P_2$ to the stalk along $e_1\circ \mathrm{toC}$ are distinct.
--
--   6. A branch-recognition clause: for every prime $P$ of $S$ omitting at least one of $\mathrm{mk}_S(X_0),\mathrm{mk}_S(X_1)$, containing $\mathrm{mk}_S(C(\sigma_1\varpi))$, and containing an element $\mathrm{mk}_S(C(1)X_0+C(0)X_1+h)$ with $h\in(X_0,X_1)^2$, and every $a\in C$: the image $\mathrm{toC}(\mathrm{germ}_Y a)$ lies in the contraction of $P$ along $e_1$ if and only if every Laurent coefficient of $a$, as an element of $\mathrm{LaurentSeries}\,L$, is the image of an element of $\mathfrak m_A$.
--
--   7. A normalisation clause at the cusp parameter: the element [`ModularCurve.jqNModC L (q*ℓ)`](def/ModularCurve_JqCoeff.html#L18) lies in $K$ and in $C$, and there exist $a_0\in A$ with the difference of that element and $a_0$ in $y'.\mathrm{asIdeal}$, an integer $e_0\ge1$ and $h\in(X_0,X_1)^{e_0}$ such that: for all $a,b\in W_1$, at least one of which is a unit, with $a^qb-ab^q\in\mathfrak m_{W_1}$, the sum $\sum_{i=0}^{e_0}\mathrm{coeff}_{(i,e_0-i)}(h)\,a^ib^{e_0-i}$ is a unit of $W_1$; and $e_1(\mathrm{toC}(\mathrm{germ}_Y(\text{that element}-a_0)))=\mathrm{mk}_S(h)$.
--
--   **The centre and the chart.** Let $J\subseteq C$ be the ideal which, by `hJ`, is the infimum of the set of ideals $J'$ of $C$ of the form $J'=\tau^{-1}\bigl((e_1\circ\mathrm{toC}\circ\mathrm{germ}_Y)^{-1}\bigl(\mathrm{mk}_S(C(\sigma_1\varpi_t)),\mathrm{mk}_S(X_0),\mathrm{mk}_S(X_1)\bigr)\bigr)$, where $\gamma$ runs over $\Gamma(q)\cap\Gamma_0(M')$ and $\tau$ over the level automorphisms at $\gamma^{-1}$ preserving $C$, and the contraction along $\tau$ is taken through its restriction to $C$. Let $B$ be the $A$-subalgebra of $K$ given by `hB` as the restriction of scalars to $A$ of
--   $$B=C\bigl[\{x\in K:\ \exists\, i\in J,\ x\,\varpi_t=i\}\bigr],$$
--   the weighted blow-up chart $C[J/\varpi_t]$ obtained by adjoining to $C$ all quotients $i/\varpi_t$ with $i\in J$.
--
--   **Conclusion.** The fibre of the $A$-algebra $B$ over the maximal ideal of $A$, namely `(IsLocalRing.maximalIdeal A).Fiber ↥B`, is a formally smooth algebra over the residue field `(IsLocalRing.maximalIdeal A).ResidueField` of that maximal ideal.
--
--   This is the special-fibre input for the fibrewise criterion of smoothness applied to the weighted blow-up chart $B=C[J/\varpi_t]$ of the $j$-finite chart algebra at a supersingular point whose completed local ring is presented by a Drinfeld-type equation. Together with the corresponding statement over the generic point it feeds the formal smoothness of $B$ itself in [`ModularCurve.FullLevel.AuxLevel.formallySmooth_blowupChart_of_drinfeldChartWitness`](thm.html#ModularCurve.FullLevel.AuxLevel.formallySmooth_blowupChart_of_drinfeldChartWitness), part of the construction of a regular integral model of the modular curve of level $\Gamma_H$ used in the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_formallySmooth_fiber_maximalIdeal_blowupChart_of_drinfeldChartWitness.lean

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

theorem ModularCurve.FullLevel.AuxLevel.formallySmooth_fiber_maximalIdeal_blowupChart_of_drinfeldChartWitness
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
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
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → γ ∈ CongruenceSubgroup.Gamma ℓ →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
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
                  (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧

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

        (∃ (hjK : ModularCurve.jqNModC L (q * ℓ) ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W₁, (a ∉ IsLocalRing.maximalIdeal W₁ ∨ b ∉ IsLocalRing.maximalIdeal W₁) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W₁ →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e₁ : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (J : Ideal ↥(chartAlgFin A (↥K) j))
    (hJ :
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
        J = sInf {J' : Ideal ↥(chartAlgFin A (↥K) j) | ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q)
          (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
          (_ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)
          (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
          J' = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres)
            (Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY))
              (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}))})

    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A) :

        Algebra.FormallySmooth (IsLocalRing.maximalIdeal A).ResidueField ((IsLocalRing.maximalIdeal A).Fiber ↥B) := by sorry
