-- Prove2me | Theorems.Thm_LogGammaPolymer_Variance_lemma_5_5_i
-- name    : LogGammaPolymer.Variance.lemma_5_5_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:31.764321+00:00
-- url     : https://prove2.me/theorems/3dcd54ed-6857-4889-b33b-3510afe16ff7
-- title:
--   Lemma 5.5(i) — limsup_N ℙ[Z_{m,n}(0 < ξ_x ≤ aN^{2/3}) / Z^□_{(1,1),(m,n)} ≥ se^{bN^{1/3}}] ≤ ε
-- statement:
--   Assume (2.4) with parameters $0<\theta<\mu$ and rectangle dimensions (2.6) with parameter $\gamma>0$. Let $a,b,s>0$ and $0<\varepsilon<1$. There exists a constant $C=C(\theta,\mu,\gamma)<\infty$ such that, if
--   $$b\ge C\varepsilon^{-1/2}(a+\sqrt a)\qquad(5.18),$$
--   then
--   $$\varlimsup_{N\to\infty}\ \mathbb P\Bigl[\frac{Z_{m,n}(0<\xi_x\le aN^{2/3})}{Z^\square_{(1,1),(m,n)}}\ge s\,e^{bN^{1/3}}\Bigr]\le\varepsilon\qquad(5.19).$$
--
--   Paths that leave along the $x$-axis but exit it before distance $aN^{2/3}$ carry, with high probability, at most $e^{bN^{1/3}}$ times the weight of the bulk partition function. This is the second step of Proposition 5.3.
--
--   **Formalization Note** $C$ is chosen before $\varepsilon,a,b,s$. The upper limit is taken along every choice of $(m,n)$ satisfying (2.6) for each $N$, and is stated as: for every $\eta>0$ there is $N_0$ with $\mathbb P[\dots]\le\varepsilon+\eta$ for all $N\ge N_0$, all such $(m,n)$ and every environment satisfying (2.4). This is equivalent to the printed upper limit, since the probability depends only on the law of the environment, which (2.4) fixes. $\mathbb P$ is the probability of the environment.
-- source:
--   Seppäläinen, Scaling for a one-dimensional directed polymer with boundary conditions, arXiv:0911.2446v4, Lemma 5.5(i), (5.18)–(5.19), p. 31

import Mathlib
import Definitions.Def_LogGammaPolymer_Variance_Paths
import Definitions.Def_LogGammaPolymer_Variance_Environment
open MeasureTheory ProbabilityTheory

namespace LogGammaPolymer.Variance

theorem lemma_5_5_i {θ μ γ : ℝ} (hθ : 0 < θ) (hθμ : θ < μ) (hγ : 0 < γ) :
    ∃ C : ℝ, ∀ a b s : ℝ, 0 < a → 0 < b → 0 < s → ∀ ε : ℝ, 0 < ε → ε < 1 →
      C * ε ^ (-(1 : ℝ) / 2) * (a + Real.sqrt a) ≤ b →
      ∀ η : ℝ, 0 < η → ∃ N₀ : ℝ,
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (E : Env θ μ P) (N : ℝ), N₀ ≤ N → ∀ m n : ℕ, InRect θ μ γ N m n →
          P.real {ω | s * Real.exp (b * N ^ ((1 : ℝ) / 3)) ≤
              Zr (E.conf ω) m n (fun x => 0 < ξx x.1 ∧ (ξx x.1 : ℝ) ≤ a * N ^ ((2 : ℝ) / 3)) /
                Zbox (E.conf ω) 1 1 m n} ≤ ε + η := by sorry

end LogGammaPolymer.Variance
