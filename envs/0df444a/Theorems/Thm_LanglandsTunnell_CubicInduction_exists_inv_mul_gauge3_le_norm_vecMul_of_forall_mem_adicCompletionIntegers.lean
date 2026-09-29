-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_inv_mul_gauge3_le_norm_vecMul_of_forall_mem_adicCompletionIntegers
-- name    : LanglandsTunnell.CubicInduction.exists_inv_mul_gauge3_le_norm_vecMul_of_forall_mem_adicCompletionIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/71f9a18f-ab0e-5ace-a1cd-0e7b514c2336
-- title:
--   Gauge lower bound for adelically moved rational vectors
-- statement:
--   Let $g$ be an element of `AdelicGL 3 (𝓞 ℚ) ℚ`, i.e. of the general linear group $\mathrm{GL}_3$ over the adele ring $\mathbb{A} =$ `AdeleRing (𝓞 ℚ) ℚ`, let $N$ be a natural number with $N > 0$, and let $\xi : \mathrm{Fin}\,3 \to \mathbb{Q}$ be a non-zero row vector. Form the adelic row vector $\xi g$, where the entries $\xi_i$ are pushed into $\mathbb{A}$ by the structure map $\mathbb{Q} \to \mathbb{A}$ and $g$ is viewed as a $3 \times 3$ matrix over $\mathbb{A}$. Assume that for every index $j$ and every $w$ in the height one spectrum of $\mathcal{O}_\mathbb{Q}$, the $w$-component of $N$ times the finite part (the second factor of the adele ring) of $(\xi g)_j$ lies in the valuation ring `w.adicCompletionIntegers ℚ` of the completion at $w$. Then there is an index $j \in \mathrm{Fin}\,3$ with $$\bigl(N \cdot \mathrm{gauge3}\,\mathbb{Q}\,g\bigr)^{-1} \le \bigl\| \bigl((\xi g)_j\bigr)_{\!1}\,\mathrm{Rat.infinitePlace} \bigr\|,$$ the right-hand side being the norm of the component, at the unique infinite place of $\mathbb{Q}$, of the infinite part (the first factor of the adele ring) of $(\xi g)_j$. Here `gauge3 ℚ g` is $\max\bigl(1, \mathrm{archGauge3}\,\mathbb{Q}\,g \cdot \mathrm{finGauge3}\,\mathbb{Q}\,g\bigr)$, where $\mathrm{archGauge3}$ is $1$ plus the sum over the infinite places $w$ of $\mathbb{Q}$ of the size `matrixSize` of the archimedean component of $g$ at $w$, and $\mathrm{finGauge3}$ is the finite product over the height one spectrum of $\mathcal{O}_\mathbb{Q}$ of the real numbers underlying the sup-sizes `matrixSupSize` of the components of $g$ at the finite places.
--
--   This is the Liouville-type lower bound for the first minimum, in the sup norm at the archimedean place, of the rational lattice moved by an adelic matrix $g$, the bound being the reciprocal of the denominator $N$ times the gauge (height) of $g$. It is used in the estimate [`LanglandsTunnell.CubicInduction.AdelicEpstein.epsteinPlus_le_mul_gauge3_rpow_div_sub_one`](thm.html#LanglandsTunnell.CubicInduction.AdelicEpstein.epsteinPlus_le_mul_gauge3_rpow_div_sub_one), where a bound for an adelic Epstein series in terms of the first minimum is converted into one in terms of a power of the gauge of $g$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_inv_mul_gauge3_le_norm_vecMul_of_forall_mem_adicCompletionIntegers.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Growth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem LanglandsTunnell.CubicInduction.exists_inv_mul_gauge3_le_norm_vecMul_of_forall_mem_adicCompletionIntegers
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (N : ℕ) (hN : 0 < N) (ξ : Fin 3 → ℚ) (hξ : ξ ≠ 0)
    (hint : ∀ (j : Fin 3) (w : HeightOneSpectrum (𝓞 ℚ)),
      ((N : FiniteAdeleRing (𝓞 ℚ) ℚ) *
          (Matrix.vecMul (fun i => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ i))
            (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) j).2) w ∈ w.adicCompletionIntegers ℚ) :
    ∃ j : Fin 3, ((N : ℝ) * gauge3 ℚ g)⁻¹ ≤
      ‖(Matrix.vecMul (fun i => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ i))
          (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) j).1 Rat.infinitePlace‖ := by sorry
