-- Prove2me | Theorems.Thm_GraphonMF_DenseLLN_eq_6_12_corrected
-- name    : GraphonMF.DenseLLN.eq_6_12_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:49.548242+00:00
-- url     : https://prove2.me/theorems/ed0b7607-dad3-4d87-95db-94e153632e5b
-- title:
--   (6.12), p. 3608 (corrected) — W_{2,T}(μ̄^{G̃}, μ̄) → 0 as ‖G̃ − G‖ → 0
-- statement:
--   Assume Condition 2.1, let $G$ be a graphon and let $X$ solve the graphon particle system (2.1) for $G$, with averaged law $\bar\mu=\int_I\mathcal L(X_u)\,du$. For another graphon $\tilde G$ with solution $X^{\tilde G}$ of (2.1) on the same probability space, write $\bar\mu^{\tilde G}=\int_I\mathcal L(X^{\tilde G}_u)\,du$. Then for every $\delta>0$ there is $\eta>0$ such that for every graphon $\tilde G$ with $\|\tilde G-G\|<\eta$ and every solution $X^{\tilde G}$,
--   $$W_{2,T}\big(\bar\mu^{\tilde G},\bar\mu\big)\le\delta .$$
--
--   This is the continuity step of the proof of (3.3): the averaged law depends continuously on the graphon in the operator norm.
--
--   **Formalization Note** The page prints $W_{2,T}(\bar\mu^{\tilde G},\bar\mu)\le\kappa\eta$ and cites Theorem 2.1(c). That theorem is qualitative and gives no rate linear in $\eta$, and the proof of (3.3) uses only $W_{2,T}(\bar\mu^{\tilde G},\bar\mu)\to0$ as $\|\tilde G-G\|\to0$. This corrected reading is what is formalized. The statement is made for all graphons $\tilde G$, continuous or not, because the argument through Theorem 2.1(c) does not use continuity.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3608, (6.12) (corrected reading; printed slip)

import Mathlib
import Definitions.Def_GraphonMF_DenseLLN_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.DenseLLN
theorem eq_6_12_corrected {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d : ℕ} {P : Measure Ω}
    {μ0 : GraphonMF.Stability.I → Measure (GraphonMF.Stability.State d)} {X0 : GraphonMF.Stability.I → Ω → GraphonMF.Stability.State d} {B : GraphonMF.Stability.I → ℝ≥0 → Ω → GraphonMF.Stability.State d}
    (noise : NoiseSetting P μ0 X0 B) (hT : 0 < T)
    (b : GraphonMF.Stability.State d → GraphonMF.Stability.State d → GraphonMF.Stability.State d) (σ : GraphonMF.Stability.State d → GraphonMF.Stability.State d → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (h21 : GraphonMF.Stability.Cond21 ε μ0 b σ)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d) (hX : IsGraphonSolution noise G b σ X) :
    ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ (G' : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (X' : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d), GraphonMF.Stability.IsGraphon G' →
        IsGraphonSolution noise G' b σ X' → GraphonMF.Stability.opNorm (fun u v => G' u v - G u v) < η →
        GraphonMF.Stability.W2T (mixture P X') (mixture P X) ≤ ENNReal.ofReal δ := by sorry
end GraphonMF.DenseLLN
