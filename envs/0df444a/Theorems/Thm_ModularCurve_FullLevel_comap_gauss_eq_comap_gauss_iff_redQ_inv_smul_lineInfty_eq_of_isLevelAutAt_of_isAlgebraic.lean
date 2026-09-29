-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_comap_gauss_eq_comap_gauss_iff_redQ_inv_smul_lineInfty_eq_of_isLevelAutAt_of_isAlgebraic
-- name    : ModularCurve.FullLevel.comap_gauss_eq_comap_gauss_iff_redQ_inv_smul_lineInfty_eq_of_isLevelAutAt_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/3246b6f8-eba5-532d-8c17-d5c191f26fe6
-- title:
--   Level automorphisms move the Gauss ring by P¹(𝔽_q)-translation
-- statement:
--   Let $q\ge 5$ be prime, $M'\ge 1$ with $q\nmid M'$, and let $L$ be a field of characteristic $0$, algebraic over $\mathbb{Q}$, containing a primitive $q$-th root of unity $\zeta$ for which some ring homomorphism $\iota:L\to\mathbb{C}$ sends $\zeta$ to $e^{2\pi i/q}$. Let $K\subseteq\mathrm{LaurentSeries}(L)$ be the intermediate field generated over $L$ by the coefficientwise image of the $\mathbb{Q}$-field of ratios $\mathrm{intSeriesC}\,p_f/\mathrm{intSeriesC}\,p_g$ of integral $q$-expansions of modular forms of equal weight on $\Gamma_H(q^2M')$, $H=\ker\big((\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times\big)$; let $K_0$ be the corresponding field for $\Gamma_0(M')$, assumed contained in $K$. Let $A$ be a discrete valuation ring with fraction field $L$, with $q$ in its maximal ideal and $\zeta$ in its image, and let $W_0\subseteq K$, $O_0\subseteq K_0$ be the valuation subrings of elements expressible as $x/y$ with $x,y\in A[[T]]$ and $y\not\equiv 0$ modulo the maximal ideal of $A$ (the Gauss rings). Let $\tau:\mathrm{SL}_2(\mathbb{Z})\to\mathrm{Aut}_L(K)$ be such that for $\gamma\in\Gamma_0(M')$, $\tau(\gamma)$ satisfies `IsLevelAutAt` at $\gamma^{-1}$: on every such ratio it acts, after transport by any $\iota$ as above, by the weight-$k$ slash by $\mathrm{conjElemN}\,(q^2M')\,\gamma^{-1}=\begin{pmatrix}a&b/q^2M'\\ q^2M'c&d\end{pmatrix}$. Then for $\gamma,\delta\in\Gamma_0(M')$: $\tau(\gamma)^{-1}(W_0)=\tau(\delta)^{-1}(W_0)$ iff $\bar\gamma^{-1}\cdot[1:0]=\bar\delta^{-1}\cdot[1:0]$ in $\mathbb{P}^1(\mathbb{Z}/q)$, where $\bar{\ }$ denotes entrywise reduction $\mathrm{SL}_2(\mathbb{Z})\to\mathrm{GL}_2(\mathbb{Z}/q)$; and $\tau(\gamma)^{-1}(W_0)=W_0$ iff $\bar\gamma^{-1}$ fixes $[1:0]$.
--
--   This is the stabiliser computation for the branch of the Igusa-type degeneration at $q$ attached to the cusp $\infty$: the Galois action of $\Gamma_0(M')$ on the set of Gauss valuation rings of $K$ coming from $W_0$ is equivariantly the action of $\mathrm{GL}_2(\mathbb{F}_q)$ on $\mathbb{P}^1(\mathbb{F}_q)$, with $W_0$ corresponding to the point $[1:0]$. It feeds the determination of the inertia action and of cyclicity of the relevant decomposition groups, and the identification of which points of the $j$-line lie in the supersingular set for $X_H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_comap_gauss_eq_comap_gauss_iff_redQ_inv_smul_lineInfty_eq_of_isLevelAutAt_of_isAlgebraic.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

open scoped MatrixGroups

theorem ModularCurve.FullLevel.comap_gauss_eq_comap_gauss_iff_redQ_inv_smul_lineInfty_eq_of_isLevelAutAt_of_isAlgebraic
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))

    [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle : K₀ ≤ K)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (O₀ : ValuationSubring ↥K₀)
    (hO₀ : ∀ f : ↥K₀, f ∈ O₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (τ : SL(2, ℤ) → (↥K ≃ₐ[L] ↥K))
    (hτ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') γ⁻¹ K (τ γ))
    (γ δ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (hδ : δ ∈ CongruenceSubgroup.Gamma0 M')
    :
    (W₀.comap (τ γ).toAlgHom.toRingHom = W₀.comap (τ δ).toAlgHom.toRingHom ↔
        ModularCurve.FullLevel.redQ q γ⁻¹ • (Projectivization.mk (ZMod q) (![1, 0] : Fin 2 → ZMod q) (by simp)) =
          ModularCurve.FullLevel.redQ q δ⁻¹ • (Projectivization.mk (ZMod q) (![1, 0] : Fin 2 → ZMod q) (by simp))) ∧
    (W₀.comap (τ γ).toAlgHom.toRingHom = W₀ ↔
        ModularCurve.FullLevel.redQ q γ⁻¹ • (Projectivization.mk (ZMod q) (![1, 0] : Fin 2 → ZMod q) (by simp)) = (Projectivization.mk (ZMod q) (![1, 0] : Fin 2 → ZMod q) (by simp))) := by sorry
