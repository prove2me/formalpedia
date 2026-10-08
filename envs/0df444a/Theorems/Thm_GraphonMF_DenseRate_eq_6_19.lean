-- Prove2me | Theorems.Thm_GraphonMF_DenseRate_eq_6_19
-- name    : GraphonMF.DenseRate.eq_6_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:16.048992+00:00
-- url     : https://prove2.me/theorems/1ebf731e-4c06-40fd-8dfa-7dcea0c8c744
-- title:
--   (6.19), pp. 3609–3610 — the discretization term T̃ⁿ,³_s is at most κ/n²
-- statement:
--   In the setting of Theorem 3.2 of Bayraktar–Chakraborty–Wu (graphon $G$, Condition 2.1, Condition 2.3, a solution $X$ of the graphon particle system (2.1) with $\mu_{v,s}=\mathcal L(X_v(s))$), let
--   $$\tilde T^{n,3}_s=\mathbb E\Big|\frac1n\sum_{j=1}^n\int_{\mathbb R^d}b(X_{i/n}(s),x)\,G(\tfrac in,\tfrac jn)\,\mu_{j/n,s}(dx)-\int_I\!\int_{\mathbb R^d}b(X_{i/n}(s),x)\,G(\tfrac in,v)\,\mu_{v,s}(dx)\,dv\Big|^2$$
--   be the third term of (6.16): the error of replacing the graphon integral over $v\in I$ by its Riemann sum at the labels $j/n$.
--
--   There is a constant $\kappa\in(0,\infty)$ such that for every $n$, every $i\in\{1,\dots,n\}$ and every $s\in[0,T]$,
--   $$\tilde T^{n,3}_s\le\frac{\kappa}{n^2}.$$
--
--   The page rewrites the Riemann sum as $\int_I(\cdot)(\lceil nv\rceil/n)\,dv$ and bounds the two resulting differences using the blockwise Lipschitz continuity of $G$ (Condition 2.3) and of $u\mapsto\mu_u$ (Theorem 2.1(b)).
--
--   **Formalization Note.** The term is defined with the Riemann sum as in (6.16); the identity with the $\lceil nv\rceil/n$ form is part of the proof. Lean's particle $j$ has label $(j+1)/n$, which is $\lceil nv\rceil/n$ for $v\in(j/n,(j+1)/n]$.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), https://doi.org/10.1214/22-AAP1901, pp. 3609–3610, §6.3, (6.19)

import Mathlib
import Definitions.Def_GraphonMF_DenseRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology unitInterval
open scoped ENNReal NNReal

namespace GraphonMF.DenseRate

theorem eq_6_19 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (T : ℝ≥0) (hT : 0 < T)
    (P : Measure Ω) (μ0 : I → Measure (Fin d → ℝ)) (X0 : I → Ω → (Fin d → ℝ))
    (B : I → ℝ≥0 → Ω → Fin d → ℝ) (hN : NoiseSetting P μ0 X0 B)
    (b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ))
    (sigma : (Fin d → ℝ) → (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (hε : 0 < ε) (h21 : Cond21 ε μ0 b sigma)
    (G : I → I → ℝ) (hG : IsGraphon G)
    {N : ℕ} (J : Fin N → Set I) (h23 : Cond23 μ0 G J)
    (X : I → ℝ≥0 → Ω → (Fin d → ℝ)) (hX : IsGraphonSolution T P X0 B G b sigma X) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (n : ℕ) (i : Fin n) (s : ℝ≥0), s ≤ T →
      Tt3 P G b X n i s ≤ ENNReal.ofReal (κ / (n : ℝ) ^ 2) := by sorry

end GraphonMF.DenseRate
