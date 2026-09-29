-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_le_mul_gauge3_rpow_div_sub_one
-- name    : LanglandsTunnell.CubicInduction.AdelicEpstein.epsteinPlus_le_mul_gauge3_rpow_div_sub_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/d4c5ded1-f919-59b1-8bbf-4d5ea6426392
-- title:
--   Gauge bound for the adelic Epstein integral on GL₃
-- statement:
--   Work over $\mathbb{Q}$, writing $\mathbb{A}$ for the adele ring of $\mathbb{Q}$, $\mathbb{A}_f$ for its finite adele ring, and $\hat{\mathbb{Z}}^{\times}$ for the group [`IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ`](def/IsDedekindDomain_FiniteUnitIdeles.html#L9) of units $\delta$ of $\mathbb{A}_f$ such that both $\delta$ and $\delta^{-1}$ are integral at every height-one prime. Fix a measurable space structure on $\hat{\mathbb{Z}}^{\times}$ and an arbitrary measure $du$ on it, a function $\Phi \colon \mathbb{A}^3 \to \mathbb{C}$, reals $M$ and $R_0 \ge 0$, a natural number $N > 0$, and assume: $\|\Phi(x)\| \le M$ for all $x$; whenever $\Phi(x) \ne 0$, each archimedean component $(x_i)_\infty$ has norm at most $R_0$ at the infinite place of $\mathbb{Q}$; and whenever $\Phi(x) \ne 0$, the finite part satisfies $N\,(x_i)_f \in \mathcal{O}_w$ for every $i$ and every height-one prime $w$. Let $g \in \mathrm{GL}_3(\mathbb{A})$ and $\sigma > 1$ be real. Then the $[0,\infty]$-valued quantity $$\mathrm{epsteinPlus}\,du\,\Phi\,\sigma\,g = \|\det g\|^{\sigma} \int t^{3\sigma} \int_{\hat{\mathbb{Z}}^{\times}} \sum_{0 \neq \xi \in \mathbb{Q}^3} \|\Phi(t\,u\,(\xi g))\| \, du \, \frac{dt}{t},$$ where $\|\cdot\|$ on $\det g$ is `TateGlobal.ideleNorm`, the value at $x$ of the distributive Haar character of $\mathbb{A}$, the inner integrand is the lower Lebesgue integral of $\|\Phi\|_{\mathrm{nn}}$ over $\hat{\mathbb{Z}}^{\times}$, the points are $\mathrm{point}\,t\,u\,g\,\xi$ (the idele $t\cdot u$ times the $i$-th entry of $\mathrm{vecMul}$ of the adelic diagonal of $\xi$ with $g$), and the outer integral is against the measure $t^{-1}\,dt$ on $(0,\infty)$, is bounded above by $$\mathrm{ofReal}\Bigl(\|\det g\|^{\sigma} \cdot \frac{9\,M\,(R_0\,N\,H_3(g))^{3\sigma}}{\sigma - 1}\Bigr)\cdot du(\hat{\mathbb{Z}}^{\times}),$$ where $H_3(g) = \mathrm{gauge3}\,\mathbb{Q}\,g = \max\bigl(1, \mathrm{archGauge3}(g)\cdot \mathrm{finGauge3}(g)\bigr)$, with $\mathrm{archGauge3}(g) = 1 + \sum_{w \mid \infty} \mathrm{matrixSize}$ of the archimedean component of $g$ at $w$ and $\mathrm{finGauge3}(g)$ the finite product over height-one primes $v$ of $\mathrm{matrixSupSize}$ of the component of $g$ at $v$. No measurability or integrability assumption on $\Phi$ is imposed.
--
--   This is the simple-pole bound for the adelic Epstein integral attached to a bounded test function with prescribed archimedean support and finite level, in the form which loses a power of the gauge (height) of the group element: convergence for $\sigma > 1$ with a bound of order $(\sigma - 1)^{-1}$, uniformly in $g$ up to $H_3(g)^{3\sigma}$. It feeds the Rankin–Selberg style estimate `exists_forall_sub_one_mul_lintegral_nnnorm_sq_mul_epsteinPlus_le_of_decay` in the cubic-induction part of the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_le_mul_gauge3_rpow_div_sub_one.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import Definitions.Def_LanglandsTunnell_CubicInduction_Growth
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

theorem LanglandsTunnell.CubicInduction.AdelicEpstein.epsteinPlus_le_mul_gauge3_rpow_div_sub_one
    [MeasurableSpace (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)]
    (du : Measure (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ))
    (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (M R₀ : ℝ) (hR₀ : 0 ≤ R₀) (N : ℕ) (hN : 0 < N)
    (hM : ∀ x, ‖Φ x‖ ≤ M)
    (hsupp : ∀ x, Φ x ≠ 0 → ∀ i, ‖(x i).1 Rat.infinitePlace‖ ≤ R₀)
    (hfin : ∀ x, Φ x ≠ 0 → ∀ (i : Fin 3) (w : HeightOneSpectrum (𝓞 ℚ)),
      ((N : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) * (x i).2) w ∈ w.adicCompletionIntegers ℚ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (σ : ℝ) (hσ : 1 < σ) :
    epsteinPlus du Φ σ g ≤
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ *
          (9 * M * (R₀ * N * gauge3 ℚ g) ^ (3 * σ) / (σ - 1))) * du Set.univ := by sorry
