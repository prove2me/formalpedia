-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_map_mem_chartAlgFin_of_isLevelAutAt_of_mem_Gamma0
-- name    : ModularCurve.FullLevel.map_mem_chartAlgFin_of_isLevelAutAt_of_mem_Gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/078d34b9-0e66-5a88-9243-418a91a90802
-- title:
--   Level automorphisms preserve the j-finite chart algebra
-- statement:
--   Fix nonzero naturals $m$ and $M'$ that are coprime, a field $L$ of characteristic zero, a natural number $n$ and an element $\xi \in L$ such that some ring homomorphism $\iota : L \to \mathbb{C}$ sends $\xi$ to $e^{2\pi i/n}$. Let $K$ be an intermediate field of $L((q)) =$ `LaurentSeries L` over $L$, and let $A$ be a commutative ring with algebra structures on $L$ and on $K$ forming a scalar tower. Let $j \in K$ be an element whose underlying Laurent series is the image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) (coefficientwise application of $\mathbb{Q} \to L$) of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), the series $q^{-1}\cdot(\text{the rational }j\text{-numerator power series})$, and assume $j \neq 0$ (as a `Fact`). Let $\gamma \in \Gamma_0(M') \subseteq \mathrm{SL}_2(\mathbb{Z})$ and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt L n ξ m (m ^ 2 * M') (ModularCurve.FullLevel.levelH m M') γ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29); that is, for every weight $k \in \mathbb{Z}$, all modular forms $f, g$ of weight $k$ on the image in $\mathrm{GL}_2(\mathbb{R})$ of $\Gamma_H(m^2M')$ for $H =$ `levelH m M'` (the kernel of the unit-reduction map attached to the divisibility `dvd_sq_mul m M'`), all integral power series $p_f, p_g$ whose complex images are the $q$-expansions of $f$ and $g$ with $p_g$ nonzero as a rational Laurent series, every $x \in K$ whose Laurent series is the image under `coeffEmb L` of $\hat p_f/\hat p_g$, and every $\iota : L \to \mathbb{C}$ with $\iota\xi = e^{2\pi i/n}$, one has $\iota(\tau x) \cdot \widehat{g\mid_k \gamma^{\sharp}} = \widehat{f\mid_k \gamma^{\sharp}}$ as complex Laurent series, where $\gamma^{\sharp} =$ `conjElemN m γ` is the real matrix $\begin{pmatrix} a & b/m \\ mc & d\end{pmatrix}$ for $\gamma = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$. Then for every $a \in K$ integral over $A[j] =$ `Algebra.adjoin A {j}`, the element $\tau a$ is again integral over $A[j]$; i.e. $\tau$ maps the subalgebra [`AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L142) into itself.
--
--   This records the classical fact that the level automorphisms of a full-level $q$-expansion field act on the $j$-finite chart of the normalised two-chart integral model, isolated as a statement about a single automorphism and the element $j$; the transformed $j$ satisfies the modular equation of level $m^2$, which is monic over $\mathbb{Z}[j]$. It is used in the full-level construction by the lemmas on stability of chart algebras, on blow-up charts and primes, and on orbit centres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_map_mem_chartAlgFin_of_isLevelAutAt_of_mem_Gamma0.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.map_mem_chartAlgFin_of_isLevelAutAt_of_mem_Gamma0
    (m : ℕ) [NeZero m] (M' : ℕ) [NeZero M'] (hmM' : Nat.Coprime m M')
    (L : Type) [Field L] [CharZero L] (n : ℕ) (ξ : L)
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / n))
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L n ξ m (m ^ 2 * M') (ModularCurve.FullLevel.levelH m M') γ K τ)
    (a : ↥K) (ha : a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) :
    τ a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j := by sorry
