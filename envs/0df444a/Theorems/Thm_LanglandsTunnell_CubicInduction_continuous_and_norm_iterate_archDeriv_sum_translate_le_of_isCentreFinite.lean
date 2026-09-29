-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite
-- name    : LanglandsTunnell.CubicInduction.continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/ee2c6bb0-63a5-55f3-a447-c6b7a6fae47e
-- title:
--   Continuity and uniform moderate growth of archimedean derivatives
-- statement:
--   Let $f$ be a complex-valued function on $\mathrm{GL}_3$ of the adeles of $\mathbb{Q}$ which is continuous, of moderate growth in the sense that $\|f(g)\| \le C\,\mathrm{gauge3}(g)^N$ for some constant $C$ and exponent $N$ and all $g$ (the gauge being $\max(1, \mathrm{archGauge3}(g)\cdot\mathrm{finGauge3}(g))$), and archimedeanly smooth, i.e. for each $g$ the map $e \mapsto f(g\cdot\mathrm{archRealLift3}\,e)$ on real $3\times 3$ matrices is $C^\infty$ on the locus $\det e \ne 0$. Assume further that there is a finite set $s$ of functions such that for every adelic $k$ whose component at every height-one prime of $\mathcal{O}_{\mathbb{Q}}$ is $1$ and whose archimedean component lies in $\mathrm{orth3}$ (i.e. satisfies $k^{\mathsf T}k = 1$), the translate $g \mapsto f(gk)$ lies in the $\mathbb{C}$-span of $s$. Let $n$ be a natural number, $c : \mathrm{Fin}\,n \to \mathbb{C}$, and $t : \mathrm{Fin}\,n \to \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ with every $t_i$ having archimedean component $1$, and put $v(x) = \sum_i c_i f(x t_i)$. Assume $v$ is centre-finite: for each of the three operators $\mathrm{casimir1}$, $\mathrm{casimir2}$, $\mathrm{casimir3}$ built from the right archimedean derivatives $\mathrm{archDeriv}\,i\,j$ (differentiation at $s=0$ along $1 + s e_{ij}$ lifted to the archimedean place) there are $N$ and coefficients $a : \mathrm{Fin}(N+1) \to \mathbb{C}$ with $a(N) = 1$ and $\sum_m a_m \cdot (\text{operator})^{[m]} v = 0$. Then: for every finite word $w$ in pairs $(i,j) \in \mathrm{Fin}\,3 \times \mathrm{Fin}\,3$, the iterated derivative obtained by folding $\mathrm{archDeriv}$ over $w$ applied to $v$ is continuous; and there exists a single natural number $N$ such that for every such word $w$ there is a real constant $C$ with $\|(\partial_w v)(g)\| \le C\,\mathrm{gauge3}(g)^N$ for all $g$.
--
--   This is the uniform moderate growth property of a $K$-finite, centre-finite smooth function on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$: all iterated archimedean derivatives of the combination of translates are continuous and bounded by a fixed power of the gauge, with only the constant depending on the differential operator. It feeds the analytic estimates for Whittaker functions and cuspidality along parabolics in the cubic induction, being used in the results on the ray order of Whittaker coefficients and on cuspidality of the iterated derivatives.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite)

theorem
LanglandsTunnell.CubicInduction.continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (hmg : IsModerateGrowth3 ℚ f)
    (hsa : WhittakerBlock.IsArchSmooth3 f)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1)
    (hz : IsCentreFinite (fun x => ∑ i, c i * f (x * t i))) :
    (∀ w : List (Fin 3 × Fin 3),
        Continuous
          (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun x => ∑ i, c i * f (x * t i)) w)) ∧
      ∃ N : ℕ, ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun x => ∑ i, c i * f (x * t i)) w g‖ ≤
          C * gauge3 ℚ g ^ N := by sorry
