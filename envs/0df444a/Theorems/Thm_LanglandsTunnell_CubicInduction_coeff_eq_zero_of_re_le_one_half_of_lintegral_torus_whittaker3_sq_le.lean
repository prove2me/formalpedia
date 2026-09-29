-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_coeff_eq_zero_of_re_le_one_half_of_lintegral_torus_whittaker3_sq_le
-- name    : LanglandsTunnell.CubicInduction.coeff_eq_zero_of_re_le_one_half_of_lintegral_torus_whittaker3_sq_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/f2a4f1d8-208b-562f-80b1-2abed3f42656
-- title:
--   Vanishing of subcritical coefficients in a GL₃ Whittaker expansion
-- statement:
--   Let $F$ be a complex-valued function on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, and write $W_F(g)$ for the triple integral $\int\!\!\int\!\!\int F(u(x,y,z)g)\,\psi_{\mathbb{Q}}(-(x+y))$, where $u(x,y,z)$ is the upper unipotent matrix with entries $x,y,z$ above the diagonal, $\psi_{\mathbb{Q}}$ is the standard additive character of $\mathbb{A}_{\mathbb{Q}}$ (archimedean times finite part), and each variable runs over the adeles against the probability measure obtained by conditioning adelic additive Haar measure to the adelic box (a fundamental domain for the Minkowski lattice at the infinite place times the integral finite adeles). For $a\colon \mathrm{Fin}\,3 \to \mathbb{R}$ let $\mathrm{diag}(a)$ denote the element of $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ obtained by placing the real diagonal matrix at the infinite place (and $1$ if the resulting matrix fails to be a unit). Given $n, J \in \mathbb{N}$, an injective family $e \colon \mathrm{Fin}\,n \to \mathbb{C}$ of exponents, coefficient functions $c_{ij}(y_2,k)$ jointly continuous on $\{y_2 > 0\}\times\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, and $\tau > 1/2$, assume the expansion hypothesis: for every compact $K$ and every $b \ge 1$ there is $C$ with $\bigl|W_F(\mathrm{diag}(y_1y_2,y_2,1)k) - \sum_{i,j} c_{ij}(y_2,k)\,y_1^{e_i}(\log y_1)^{j}\bigr| \le C y_1^{\tau}$ for all $k \in K$, $b^{-1}\le y_2 \le b$, $0 < y_1 \le 1$. Let $B \subseteq \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, let $\Phi$ be a complex function of a triple of adeles, and let $b_0 > 1$, $\varphi_0 > 0$ be such that $\|\Phi(j \mapsto (\mathrm{diag}(a)k)_{2j})\| \ge \varphi_0$ for all $k \in B$ and all positive $a$ with $b_0^{-1}\le a_2 \le b_0$. Assume finally a simple-pole bound: there is $C'$ with $$\int_{B}\int_{(0,\infty)^3} \|W_F(\mathrm{diag}(a)k)\|^2\,\|\Phi(j\mapsto(\mathrm{diag}(a)k)_{2j})\|\; a_0^{\sigma-3}a_1^{\sigma-1}a_2^{\sigma+1}\,da\;d\mu(k) \le \frac{C'}{\sigma-1}$$ for all $\sigma \in (1,2]$, the outer integral being the adelic Haar measure on $\mathrm{GL}_3$ and both integrals taken as lower Lebesgue integrals in $[0,\infty]$. Then for every $i$ and $j$ with $\mathrm{Re}\,e_i < 1/2$, or with $\mathrm{Re}\,e_i = 1/2$ and $j \ge 1$, one has $c_{ij}(y_2,k) = 0$ for all $y_2 > 0$ and all $k$ in the interior of $B$.
--
--   This is the step which, from a mean-square bound with a simple pole at $\sigma = 1$ for the torus integral of a Whittaker coefficient on $\mathrm{GL}_3$ weighted by a factor bounded away from zero, excludes from the asymptotic expansion along the direction $\mathrm{diag}(y_1y_2,y_2,1)$ all exponents of real part below $1/2$ together with the logarithmic terms at real part exactly $1/2$. It combines a localisation of the mean-square bound to the expansion with the one-variable vanishing criterion for sums $\sum d_{ij}y^{e_i}(\log y)^j$, and feeds the growth estimates used in the cubic induction for Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_coeff_eq_zero_of_re_le_one_half_of_lintegral_torus_whittaker3_sq_le.lean

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
LanglandsTunnell.CubicInduction.coeff_eq_zero_of_re_le_one_half_of_lintegral_torus_whittaker3_sq_le
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
            ENNReal.ofReal (C' / (σ - 1)))) :
    ∀ (i : Fin n) (j : Fin J), ((e i).re < 1 / 2 ∨ ((e i).re = 1 / 2 ∧ 1 ≤ (j : ℕ))) →
      ∀ y₂ : ℝ, 0 < y₂ → ∀ k ∈ interior B, c i j y₂ k = 0 := by sorry
