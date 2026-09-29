-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_nhds_lintegral_sum_cpow_log_sq_le_of_lintegral_torus_whittaker3_sq_le
-- name    : LanglandsTunnell.CubicInduction.exists_nhds_lintegral_sum_cpow_log_sq_le_of_lintegral_torus_whittaker3_sq_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/34469ca1-7b8e-5097-ab2e-8fe379044446
-- title:
--   Mean-square bound on a box for the Whittaker expansion terms
-- statement:
--   Fix a function $F$ on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, and let $W(g)$ denote the value at $g$ of the triple integral $\int\!\int\!\int F(u(x,y,z)g)\,\psi_{\mathbb{Q}}(-(x+y))$, taken against the conditional probability measure obtained from adelic additive Haar measure on the adelic box of $\mathbb{Q}$, where $u(x,y,z)$ is the upper unipotent matrix with entries $x,y,z$ and $\psi_{\mathbb{Q}}$ is the standard global additive character; the remaining data of the carrier (empty set, trivial subgroups, unit generators) are fixed as indicated. Let $n, J \in \mathbb{N}$, let $e : \mathrm{Fin}\,n \to \mathbb{C}$ be injective, and let $c_{ij} : \mathbb{R} \times \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ be continuous on $\{y_2 > 0\}$. Let $\tau > 1/2$, and assume that for every compact $K$ and every $b \ge 1$ there is $C$ with $\bigl\| W(\mathrm{diag}(y_1y_2,y_2,1)_{\infty}k) - \sum_{i,j} c_{ij}(y_2,k)\,y_1^{e_i}(\log y_1)^j \bigr\| \le C y_1^{\tau}$ for all $k \in K$, $b^{-1} \le y_2 \le b$ and $0 < y_1 \le 1$, where $\mathrm{diag}(\cdot)_{\infty}$ denotes the invertible adelic matrix obtained from a real diagonal matrix by the archimedean inclusion and $y_1^{e_i}$ is a complex power. Let $B$ be a set of adelic matrices, $\Phi$ a complex function on $\mathbb{A}_{\mathbb{Q}}^3$, $b_0 > 1$ and $\varphi_0 > 0$, and assume $\varphi_0 \le \|\Phi(\text{third row of } \mathrm{diag}(a)_{\infty}k)\|$ for all $k \in B$ and all $a \in \mathbb{R}_{>0}^3$ with $b_0^{-1} \le a_2 \le b_0$. Assume further that there is $C'$ with $$\int_{k \in B}\int_{a \in (0,\infty)^3} \|W(\mathrm{diag}(a)_{\infty}k)\|^2\,\|\Phi(\text{third row of }\mathrm{diag}(a)_{\infty}k)\|\,a_0^{\sigma-3}a_1^{\sigma-1}a_2^{\sigma+1}\,\mathrm{d}a\,\mathrm{d}k \le \frac{C'}{\sigma-1}$$ for every $\sigma \in (1,2]$, the inner integral being a lower Lebesgue integral and the outer one taken against the Haar measure on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ for its Borel structure. Then for every $k_0$ in the interior of $B$ and every $b \ge 1$ there exist a compact set $N \subseteq B$ that is a neighbourhood of $k_0$ and a constant $C''$ such that, for all $\sigma \in (1,2]$, $$\int_{k \in N}\int_{b_0^{-1}}^{b_0}\int_{b^{-1}}^{b}\int_{0}^{1} \Bigl\| \sum_{i,j} c_{ij}\bigl(y_2,\ \mathrm{diag}(z,z,z)_{\infty}k\bigr) y_1^{e_i}(\log y_1)^j \Bigr\|^2 y_1^{\sigma-3}\,\mathrm{d}y_1\,\mathrm{d}y_2\,\mathrm{d}z\,\mathrm{d}k \le \frac{C''}{\sigma-1},$$ with the three inner integrals lower Lebesgue integrals over $(0,1]$, $[b^{-1},b]$ and $[b_0^{-1},b_0]$ respectively and the outer one against the same Haar measure.
--
--   This is the bookkeeping transition, in the Jacquet–Shalika style analysis of $\mathrm{GL}_3$ Whittaker functions, from a simple-pole bound for the torus mean square of a Whittaker coefficient to the corresponding mean-square bound for the finite sum of terms $y_1^{e_i}(\log y_1)^j$ appearing in its asymptotic expansion, over a box around an interior point of the translate set. It feeds the conclusion that expansion coefficients with exponent of real part at most $1/2$ vanish, used in [`LanglandsTunnell.CubicInduction.coeff_eq_zero_of_re_le_one_half_of_lintegral_torus_whittaker3_sq_le`](thm.html#LanglandsTunnell.CubicInduction.coeff_eq_zero_of_re_le_one_half_of_lintegral_torus_whittaker3_sq_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_nhds_lintegral_sum_cpow_log_sq_le_of_lintegral_torus_whittaker3_sq_le.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmooth3
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory NumberField.StandardAddChar
open LanglandsTunnell.CubicInduction
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

theorem
LanglandsTunnell.CubicInduction.exists_nhds_lintegral_sum_cpow_log_sq_le_of_lintegral_torus_whittaker3_sq_le
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (n J : ℕ) (e : Fin n → ℂ) (he : Function.Injective e)
    (c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1})
    (τ : ℝ) (hτ : 1 / 2 < τ)
    (hexp : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ F
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ)
    (B : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
    (b₀ : ℝ) (hb₀ : 1 < b₀) (φ₀ : ℝ) (hφ₀ : 0 < φ₀)
    (hΦ : ∀ k ∈ B, ∀ a : Fin 3 → ℝ, (∀ i, 0 < a i) → b₀⁻¹ ≤ a 2 → a 2 ≤ b₀ →
      φ₀ ≤ ‖Φ fun j : Fin 3 => ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k :
                    AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖)
    (hZ : ∃ C' : ℝ, ∀ σ : ℝ, σ ∈ Set.Ioc (1 : ℝ) 2 →
        (letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
          ∫⁻ k in B, (∫⁻ a in Set.pi Set.univ (fun _ : Fin 3 => Set.Ioi (0 : ℝ)),
              (‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
                    NumberField.StandardAddChar.psiQ F
                    (WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k)‖₊ : ℝ≥0∞) ^ 2 *
                (‖Φ fun j : Fin 3 => ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k :
                    AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
                ENNReal.ofReal (a 0 ^ (σ - 3) * a 1 ^ (σ - 1) * a 2 ^ (σ + 1)) ∂volume)
            ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ≤
            ENNReal.ofReal (C' / (σ - 1))))
    (k₀ : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₀ : k₀ ∈ interior B) (b : ℝ) (hb : 1 ≤ b) :
    ∃ N : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact N ∧ N ∈ nhds k₀ ∧ N ⊆ B ∧ ∃ C'' : ℝ, ∀ σ : ℝ, σ ∈ Set.Ioc (1 : ℝ) 2 →
      ∫⁻ k in N, ∫⁻ z in Set.Icc b₀⁻¹ b₀, ∫⁻ y₂ in Set.Icc b⁻¹ b, ∫⁻ y₁ in Set.Ioc (0 : ℝ) 1,
          (‖∑ i : Fin n, ∑ j : Fin J,
              c i j y₂ (WhittakerBlock.archRealLift3 (fun i' j' => if i' = j' then z else 0) * k) *
                ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))‖₊ : ℝ≥0∞) ^ 2 *
            ENNReal.ofReal (y₁ ^ (σ - 3)) ∂volume ∂volume ∂volume
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ≤ ENNReal.ofReal (C'' / (σ - 1)) := by sorry
