-- Prove2me | Theorems.Thm_GraphonMF_DenseRate_eq_6_17
-- name    : GraphonMF.DenseRate.eq_6_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:12.542043+00:00
-- url     : https://prove2.me/theorems/47c644ad-9c9d-47b7-8a0b-6881c6f61e88
-- title:
--   (6.17), p. 3609 — T̃ⁿ,¹_s ≤ 2κ maxᵢ E|Xⁿ_i(s) − X_{i/n}(s)|²
-- statement:
--   In the setting of Theorem 3.2 of Bayraktar–Chakraborty–Wu (graphon $G$, Condition 2.1, Condition 3.2, a solution $X$ of (2.1) and solutions $X^n$ of (3.1)), let
--   $$\tilde T^{n,1}_s=\mathbb E\Big|\frac1n\sum_{j=1}^n\xi^n_{ij}\big(b(X^n_i(s),X^n_j(s))-b(X_{i/n}(s),X_{j/n}(s))\big)\Big|^2$$
--   be the first term of the decomposition (6.16) for particle $i$ at time $s$.
--
--   There is a constant $\kappa\in(0,\infty)$, independent of $n$, $i$ and $s$, such that for every $n$, every $i\in\{1,\dots,n\}$ and every $s\in[0,T]$,
--   $$\tilde T^{n,1}_s\le2\kappa\max_{i'=1,\dots,n}\mathbb E|X^n_{i'}(s)-X_{i'/n}(s)|^2.$$
--
--   This is the term that feeds back into Gronwall's inequality: it controls the effect of replacing the $n$-particle states by the continuum states inside the interaction.
--
--   **Formalization Note.** The maximum over particles is a supremum over `Fin n`; only the final inequality of (6.17) is stated, with the constant written $2\kappa$ as printed.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), https://doi.org/10.1214/22-AAP1901, p. 3609, §6.3, (6.17)

import Mathlib
import Definitions.Def_GraphonMF_DenseRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology unitInterval
open scoped ENNReal NNReal

namespace GraphonMF.DenseRate

theorem eq_6_17 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (T : ℝ≥0) (hT : 0 < T)
    (P : Measure Ω) (μ0 : I → Measure (Fin d → ℝ)) (X0 : I → Ω → (Fin d → ℝ))
    (B : I → ℝ≥0 → Ω → Fin d → ℝ) (hN : NoiseSetting P μ0 X0 B)
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
    (b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ))
    (sigma : (Fin d → ℝ) → (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (hε : 0 < ε) (h21 : Cond21 ε μ0 b sigma)
    (G : I → I → ℝ) (hG : IsGraphon G)
    (h32 : Cond32 P X0 B ξ G)
    (X : I → ℝ≥0 → Ω → (Fin d → ℝ)) (hX : IsGraphonSolution T P X0 B G b sigma X) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (n : ℕ) (Xn : Fin n → ℝ≥0 → Ω → (Fin d → ℝ)),
      IsParticleSolution T P X0 B ξ b sigma n Xn → ∀ (i : Fin n) (s : ℝ≥0), s ≤ T →
      Tt1 P ξ b X n Xn i s ≤
        ENNReal.ofReal (2 * κ) * ⨆ i' : Fin n, ∫⁻ ω, ‖Xn i' s ω - X (lab n i') s ω‖ₑ ^ 2 ∂P := by sorry

end GraphonMF.DenseRate
