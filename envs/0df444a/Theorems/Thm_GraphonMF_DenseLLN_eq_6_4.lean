-- Prove2me | Theorems.Thm_GraphonMF_DenseLLN_eq_6_4
-- name    : GraphonMF.DenseLLN.eq_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:23.817183+00:00
-- url     : https://prove2.me/theorems/f42f8ae8-7b35-498c-9ad3-6403f94db19f
-- title:
--   (6.4), p. 3605 — the weak-LLN term T^{n,2}_s is at most κ/n, uniformly in s ≤ T
-- statement:
--   Assume Condition 2.1, let $G$ be a graphon and let $X=(X_u)$ solve the graphon particle system (2.1) with laws $\mu_u$. Let $G_n$ be step graphons and $\xi^n_{ij}$ weights satisfying Condition 3.1(a) and (b). Consider the term of the decomposition (6.2)
--   $$\mathcal T^{n,2}_s=\frac1n\sum_{i=1}^n\mathbb E\Big|\frac1n\sum_{j=1}^n\Big(\xi^n_{ij}\,b(X_{i/n}(s),X_{j/n}(s))-\int_{\mathbb R^d}b(X_{i/n}(s),x)\,G_n(\tfrac in,\tfrac jn)\,\mu_{j/n,s}(dx)\Big)\Big|^2 .$$
--   Then there is a constant $\kappa$ such that for all such $(G_n)$, $(\xi^n)$, all $n$ and all $s\in[0,T]$,
--   $$\mathcal T^{n,2}_s\le\frac{\kappa}{n}.$$
--
--   This is the law-of-large-numbers step in the proof of Lemma 6.1: given $X_{i/n}$, the summands over $j$ are centred and independent, so only the diagonal pairs contribute.
--
--   **Formalization Note** The constant is chosen before the sequences $(G_n)$, $(\xi^n)$, $n$ and $s$. The page bounds it by the boundedness of $\xi^n_{ij}$ and $G_n$, the Lipschitz property of $b$ and the uniform second moment of $X_u$, none of which depends on the sequence. The intermediate equalities of the display are proof steps and are not stated. At $n=0$ both sides are degenerate ($0\le\infty$). Each $\xi^n$ is assumed measurable: on the page the weights are random variables, and the hypothesis excludes non-measurable maps for which the independence clauses of Condition 3.1(b.2) would refer to outer measures.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3605, (6.4) (with (6.2), pp. 3604–3605)

import Mathlib
import Definitions.Def_GraphonMF_DenseLLN_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.DenseLLN
theorem eq_6_4 {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d : ℕ} {P : Measure Ω}
    {μ0 : GraphonMF.Stability.I → Measure (GraphonMF.Stability.State d)} {X0 : GraphonMF.Stability.I → Ω → GraphonMF.Stability.State d} {B : GraphonMF.Stability.I → ℝ≥0 → Ω → GraphonMF.Stability.State d}
    (noise : NoiseSetting P μ0 X0 B) (hT : 0 < T)
    (b : GraphonMF.Stability.State d → GraphonMF.Stability.State d → GraphonMF.Stability.State d) (σ : GraphonMF.Stability.State d → GraphonMF.Stability.State d → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (h21 : GraphonMF.Stability.Cond21 ε μ0 b σ)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d) (hX : IsGraphonSolution noise G b σ X) :
    ∃ κ : ℝ, ∀ (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ),
      (∀ n, Measurable (ξ n)) →
      (∀ n, 0 < n → GraphonMF.Stability.IsStepGraphon n (Gs n)) → Cond31b P X0 B ξ Gs →
      ∀ (n : ℕ) (s : ℝ≥0), s ≤ T → Tn2 P b X ξ Gs n s ≤ ENNReal.ofReal κ / n := by sorry
end GraphonMF.DenseLLN
