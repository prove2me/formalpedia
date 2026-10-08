-- Prove2me | Theorems.Thm_GraphonMF_DenseLLN_lemma_6_1
-- name    : GraphonMF.DenseLLN.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:53.856324+00:00
-- url     : https://prove2.me/theorems/77a797c3-023c-4ad2-aa2d-6b8bc2c55289
-- title:
--   Lemma 6.1, p. 3604 — limsup (1/n) Σᵢ E‖Xⁿ_i − X_{i/n}‖²_{*,T} ≤ κ(M) limsup ‖G_n − G‖ + κ/M^ε
-- statement:
--   Assume Conditions 2.1 and 2.2 (for a cover $I_1,\dots,I_N$), let $G$ be a graphon and let $X=(X_u)$ solve the graphon particle system (2.1). Then there exist constants $\kappa$ and, for each $M\in(0,\infty)$, $\kappa(M)$ with the following property. Let $(G_n)$ be step graphons and $(\xi^n_{ij})$ weights satisfying Condition 3.1(a), (b), and let $X^n=(X^n_1,\dots,X^n_n)$ solve the $n$-particle system (3.1) for every $n$. Then
--   $$\limsup_{n\to\infty}\frac1n\sum_{i=1}^n\mathbb E\big\|X^n_i-X_{i/n}\big\|_{*,T}^2\le\kappa(M)\limsup_{n\to\infty}\|G_n-G\|+\frac{\kappa}{M^{\varepsilon}},$$
--   where $\|\cdot\|$ is the operator norm $L^\infty(I)\to L^1(I)$ of Remark 2.1.
--
--   The $n$-particle system and the graphon system are driven by the same initial states and Brownian motions, so the difference is pathwise. Under Condition 3.1(c) and Remark 2.1, letting $M\to\infty$ gives (3.4). The proof of (3.3) applies the lemma again with a continuous approximation $\tilde G$ in place of $G$.
--
--   **Formalization Note** The constants $\kappa$, $\kappa(M)$ are chosen before the sequences $(G_n)$, $(\xi^n)$ and the solutions $X^n$. This is the reading under which the page applies the lemma with one limit and several sequences (p. 3608); with constants chosen after the sequence the statement would be nearly empty. Condition 3.1(c) is not a hypothesis. Positivity of the constants is not asserted. Each $\xi^n$ is assumed measurable, which the definition of the $n$-particle filtration needs.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3604, Lemma 6.1

import Mathlib
import Definitions.Def_GraphonMF_DenseLLN_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.DenseLLN
theorem lemma_6_1 {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d N : ℕ} {P : Measure Ω}
    {μ0 : GraphonMF.Stability.I → Measure (GraphonMF.Stability.State d)} {X0 : GraphonMF.Stability.I → Ω → GraphonMF.Stability.State d} {B : GraphonMF.Stability.I → ℝ≥0 → Ω → GraphonMF.Stability.State d}
    (noise : NoiseSetting P μ0 X0 B) (hT : 0 < T)
    (b : GraphonMF.Stability.State d → GraphonMF.Stability.State d → GraphonMF.Stability.State d) (σ : GraphonMF.Stability.State d → GraphonMF.Stability.State d → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (h21 : GraphonMF.Stability.Cond21 ε μ0 b σ)
    (J : Fin N → Set GraphonMF.Stability.I) (h22a : Cond22a μ0 J)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G) (h22b : Cond22b G J)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d) (hX : IsGraphonSolution noise G b σ X) :
    ∃ κ : ℝ, ∀ M : ℝ, 0 < M → ∃ κM : ℝ,
      ∀ (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
        (hξ : ∀ n, Measurable (ξ n)) (Xn : (n : ℕ) → Fin n → Ω → GraphonMF.Stability.Cd T d),
      (∀ n, 0 < n → GraphonMF.Stability.IsStepGraphon n (Gs n)) → Cond31b P X0 B ξ Gs →
      (∀ n, IsParticleSolution noise b σ n (ξ n) (hξ n) (Xn n)) →
      limsup (fun n : ℕ => (1 / (n : ℝ≥0∞)) *
          ∑ i : Fin n, ∫⁻ ω, ‖Xn n i ω - X (GraphonMF.Stability.lab n i) ω‖ₑ ^ 2 ∂P) atTop ≤
        ENNReal.ofReal κM *
            limsup (fun n => ENNReal.ofReal (GraphonMF.Stability.opNorm (fun u v => Gs n u v - G u v))) atTop +
          ENNReal.ofReal (κ / M ^ ε) := by sorry
end GraphonMF.DenseLLN
