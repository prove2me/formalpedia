-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_le_div_sub_one_of_forall_exists_le_norm_vecMul
-- name    : LanglandsTunnell.CubicInduction.AdelicEpstein.epsteinPlus_le_div_sub_one_of_forall_exists_le_norm_vecMul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/1a329a69-eccd-5db2-b805-e0291db0023e
-- title:
--   Simple-pole bound for the adelic Epstein integral on GL₃
-- statement:
--   Write $\mathbb{A}$ for the adele ring of $\mathbb{Q}$, $\mathbb{A}_f$ for its finite adeles, and $\hat{\mathbb{Z}}^\times$ for the subgroup [`IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ`](def/IsDedekindDomain_FiniteUnitIdeles.html#L9) of those units of $\mathbb{A}_f$ all of whose components, and all of whose inverse's components, lie in the local integers; fix an arbitrary $\sigma$-algebra on this group and an arbitrary measure $du$ on it. Let $\Phi \colon \mathbb{A}^3 \to \mathbb{C}$, let $M, R_0, r \in \mathbb{R}$ with $0 \le R_0$ and $0 < r$, and assume: $\|\Phi(x)\| \le M$ for all $x$; whenever $\Phi(x) \ne 0$, the component of each $x_i$ at the archimedean completion of $\mathbb{Q}$ has norm at most $R_0$. Let $L$ be an additive subgroup of $\mathbb{A}_f^3$ such that the finite part $(x_i)_i$ of any $x$ with $\Phi(x) \ne 0$ lies in $L$, and such that $L$ is stable under coordinatewise multiplication by every element of $\hat{\mathbb{Z}}^\times$. Let $g \in \mathrm{GL}_3(\mathbb{A})$ and suppose that for every nonzero $\xi \in \mathbb{Q}^3$ whose moved vector $\xi g$ (the row vector $\xi$, pushed into $\mathbb{A}^3$ by $\mathbb{Q} \to \mathbb{A}$, multiplied on the right by $g$) has finite part in $L$, some coordinate of $\xi g$ has archimedean component of norm at least $r$. Then, for every real $\sigma > 1$, the $[0,\infty]$-valued Epstein integral $$\|\det g\|^{\sigma} \int_{0}^{\infty} t^{3\sigma} \int_{\hat{\mathbb{Z}}^\times} \sum_{0 \ne \xi \in \mathbb{Q}^3} \|\Phi\bigl((t u)\cdot \xi g\bigr)\|\, du\, \frac{dt}{t},$$ with $\|\det g\|$ the idele norm given by the module of the distributive Haar character, $t u$ the idele with archimedean part $t$ and finite part $u$, and all sums and integrals taken in $[0,\infty]$, is bounded above by $\mathrm{ofReal}\bigl(\|\det g\|^{\sigma} \cdot 9 M (R_0/r)^{3\sigma}/(\sigma-1)\bigr)$ times $du(\hat{\mathbb{Z}}^\times)$.
--
--   This is the upper-bound half of the classical convergence statement for the Epstein zeta function of a lattice in $\mathbb{R}^3$ in the range $\mathrm{Re}\,s > 3$ (here $s = 3\sigma$), in the adelic normalisation used for Rankin–Selberg unfolding on $\mathrm{GL}_3$: the only information about $g$ that enters is the lower bound $r$ for the shortest vector, in the sup norm at the real place, of the rational lattice moved by $g$ and cut out by $L$. It feeds the bound `epsteinPlus_le_mul_gauge3_rpow_div_sub_one`, where $r$ is replaced by a gauge attached to $g$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_le_div_sub_one_of_forall_exists_le_norm_vecMul.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField MeasureTheory

theorem LanglandsTunnell.CubicInduction.AdelicEpstein.epsteinPlus_le_div_sub_one_of_forall_exists_le_norm_vecMul
    [MeasurableSpace (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)]
    (du : Measure (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ))
    (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (M R₀ r : ℝ) (hR₀ : 0 ≤ R₀) (hr : 0 < r)
    (hM : ∀ x, ‖Φ x‖ ≤ M)
    (hsupp : ∀ x, Φ x ≠ 0 → ∀ i, ‖(x i).1 Rat.infinitePlace‖ ≤ R₀)
    (L : AddSubgroup (Fin 3 → IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))
    (hL : ∀ x, Φ x ≠ 0 → (fun i => (x i).2) ∈ L)
    (hLu : ∀ (u : IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)
      (z : Fin 3 → IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ), z ∈ L →
        (fun i => ((u : (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) * z i) ∈ L)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hsep : ∀ ξ : Fin 3 → ℚ, ξ ≠ 0 →
      (fun i => (Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i).2) ∈ L →
        ∃ i, r ≤ ‖(Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i).1
          Rat.infinitePlace‖)
    (σ : ℝ) (hσ : 1 < σ) :
    epsteinPlus du Φ σ g ≤
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ *
          (9 * M * (R₀ / r) ^ (3 * σ) / (σ - 1))) * du Set.univ := by sorry
