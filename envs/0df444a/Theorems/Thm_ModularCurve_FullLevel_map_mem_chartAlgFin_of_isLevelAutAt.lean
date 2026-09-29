-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_map_mem_chartAlgFin_of_isLevelAutAt
-- name    : ModularCurve.FullLevel.map_mem_chartAlgFin_of_isLevelAutAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/612dbd38-780a-52e5-9c58-376dd1d41645
-- title:
--   Level automorphisms preserve the j-finite integral chart
-- statement:
--   Fix nonzero naturals $m$ and $M'$, a field $L$ of characteristic zero, a natural number $n$ and an element $\xi \in L$ such that some ring homomorphism $L \to \mathbb{C}$ carries $\xi$ to $\exp(2\pi i/n)$. Let $K$ be an intermediate field of $L((q))/L$, let $A$ be a commutative ring with compatible algebra maps $A \to L \to K$, and let $j \in K$ be an element, assumed nonzero, whose Laurent series is the image under $\mathbb{Q} \to L$ of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), namely $q^{-1}$ times the rational $q$-expansion of the modular invariant. Let $H$ be a subgroup of $(\mathbb{Z}/m^{2}M')^{\times}$, let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt`](def/ModularCurve_FullLevelLevelAutAt.html#L29) for the data $L, n, \xi, m, m^{2}M', H, \gamma$: for every weight $k \in \mathbb{Z}$, all modular forms $f,g$ of weight $k$ for the image in $\mathrm{GL}_2(\mathbb{R})$ of $\Gamma_H(m^2M')$ with integral $q$-expansions given by power series $p_f, p_g$ over $\mathbb{Z}$, with the Laurent series of $p_g$ over $\mathbb{Q}$ nonzero, every $x \in K$ whose Laurent series is the image of $\hat p_f/\hat p_g$, and every $\iota : L \to \mathbb{C}$ with $\iota(\xi) = \exp(2\pi i/n)$, one has $\iota_{*}(\tau x) \cdot \widehat{g\mid_k \gamma^{\sharp}} = \widehat{f\mid_k \gamma^{\sharp}}$, where $\gamma^{\sharp}$ is the matrix $\begin{pmatrix} a & b/m \\ mc & d\end{pmatrix}$ attached to $\gamma = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$. Then for every $a \in K$ integral over the $A$-subalgebra $A[j]$ of $K$, the element $\tau a$ is again integral over $A[j]$; that is, $\tau$ maps the $j$-finite chart algebra of the two-chart integral model into itself.
--
--   This is the integrality statement underlying the fact that a level automorphism of a field of modular functions acts on the affine $j$-chart of the integral model of the $j$-line: $\tau(j)$ is a root of a modular equation of level $m^2$ and hence integral over $\mathbb{Z}[j]$, so transitivity of integrality carries the whole chart algebra into itself. It is used in the analysis of the blowup charts and of orbits of level automorphisms on the two-chart integral model, for an arbitrary level subgroup $H \le (\mathbb{Z}/m^2M')^\times$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_map_mem_chartAlgFin_of_isLevelAutAt.lean

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

theorem ModularCurve.FullLevel.map_mem_chartAlgFin_of_isLevelAutAt
    (m : ℕ) [NeZero m] (M' : ℕ) [NeZero M']
    (L : Type) [Field L] [CharZero L] (n : ℕ) (ξ : L)
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / n))
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (H : Subgroup (ZMod (m ^ 2 * M'))ˣ)
    (γ : SL(2, ℤ)) (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L n ξ m (m ^ 2 * M') H γ K τ)
    (a : ↥K) (ha : a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) :
    τ a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j := by sorry
