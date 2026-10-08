-- Prove2me | Theorems.Thm_GraphonMF_DenseRate_eq_6_18
-- name    : GraphonMF.DenseRate.eq_6_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:26.293981+00:00
-- url     : https://prove2.me/theorems/a9026e7b-5c8f-490b-81ee-ad130bf63029
-- title:
--   (6.18), p. 3609 — the weak-LLN term T̃ⁿ,²_s is at most κ/n
-- statement:
--   In the setting of Theorem 3.2 of Bayraktar–Chakraborty–Wu (graphon $G$, Condition 2.1, Condition 3.2 on the weights $\xi^n_{ij}$, a solution $X$ of the graphon particle system (2.1) with $\mu_{v,s}=\mathcal L(X_v(s))$), let
--   $$\tilde T^{n,2}_s=\mathbb E\Big|\frac1n\sum_{j=1}^n\Big(\xi^n_{ij}\,b(X_{i/n}(s),X_{j/n}(s))-\int_{\mathbb R^d}b(X_{i/n}(s),x)\,G(\tfrac in,\tfrac jn)\,\mu_{j/n,s}(dx)\Big)\Big|^2$$
--   be the second term of (6.16). It involves only the continuum particles and the weights.
--
--   There is a constant $\kappa\in(0,\infty)$ such that for every $n$, every $i\in\{1,\dots,n\}$ and every $s\in[0,T]$,
--   $$\tilde T^{n,2}_s\le\frac{\kappa}{n}.$$
--
--   This is a law-of-large-numbers estimate: the summands are, conditionally on $X_{i/n}$, centred and independent, because the continuum particles at distinct labels are independent and the weights are independent of them.
--
--   **Formalization Note.** No $n$-particle solution enters the statement. The constant is placed before $n$, $i$ and $s$.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), https://doi.org/10.1214/22-AAP1901, p. 3609, §6.3, (6.18)

import Mathlib
import Definitions.Def_GraphonMF_DenseRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology unitInterval
open scoped ENNReal NNReal

namespace GraphonMF.DenseRate

theorem eq_6_18 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (T : ℝ≥0) (hT : 0 < T)
    (P : Measure Ω) (μ0 : I → Measure (Fin d → ℝ)) (X0 : I → Ω → (Fin d → ℝ))
    (B : I → ℝ≥0 → Ω → Fin d → ℝ) (hN : NoiseSetting P μ0 X0 B)
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
    (b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ))
    (sigma : (Fin d → ℝ) → (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (hε : 0 < ε) (h21 : Cond21 ε μ0 b sigma)
    (G : I → I → ℝ) (hG : IsGraphon G)
    (h32 : Cond32 P X0 B ξ G)
    (X : I → ℝ≥0 → Ω → (Fin d → ℝ)) (hX : IsGraphonSolution T P X0 B G b sigma X) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (n : ℕ) (i : Fin n) (s : ℝ≥0), s ≤ T →
      Tt2 P ξ G b X n i s ≤ ENNReal.ofReal (κ / (n : ℝ)) := by sorry

end GraphonMF.DenseRate
