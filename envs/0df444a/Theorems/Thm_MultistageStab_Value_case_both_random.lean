-- Prove2me | Theorems.Thm_MultistageStab_Value_case_both_random
-- name    : MultistageStab.Value.case_both_random
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:14.109674+00:00
-- url     : https://prove2.me/theorems/d7ca500a-89ed-448a-a6b6-28751fa968e5
-- title:
--   Proof of Theorem 2.1, p. 7, case r = r′ = 2 — v(ξ̃) − v(ξ) ≤ L(‖ξ̃ − ξ‖_2 + Σ‖x̄_t − E[x̄_t|F̃_t]‖_2) + ε
-- statement:
--   Work in the setting of program (1) in the case $r = r' = 2$. Assume (A1), $X_1$ bounded, $\xi$ admissible, $v(\xi)$ finite, and the level-boundedness of (A2) with constants $\alpha > 0$, $\delta > 0$. Then there is a constant $L > 0$ such that for every $\varepsilon \in (0,\alpha]$, every admissible $\tilde\xi$ with $\|\tilde\xi - \xi\|_2 < \delta$ and $v(\tilde\xi)$ finite, and every $\bar x \in l_\varepsilon(F(\xi,\cdot))$,
--   $$v(\tilde\xi) - v(\xi) \le L\Big( \|\tilde\xi - \xi\|_2 + \sum_{t=2}^{T-1} \big\|\bar x_t - \mathbb E[\bar x_t \mid \tilde{\mathcal F}_t]\big\|_2 \Big) + \varepsilon .$$
--
--   This is the third case estimate in the proof of Theorem 2.1.
--
--   **Formalization Note** The case is the pattern `both`, which places no restriction on which of $b_t$, $h_t$ depend on the input; the paper's row reads "otherwise". The inequality is stated in $[0,\infty]$ with its left-hand side truncated at $0$.
-- source:
--   Heitsch, Römisch & Strugarek, Stability of multistage stochastic programs, author manuscript (edoc.hu-berlin.de, c. 2005), pp. 5, 7, proof of Theorem 2.1, case r = r′ = 2

import Mathlib
import Definitions.Def_MultistageStab_Value_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultistageStab.Value

theorem case_both_random (D : Data) (hpat : Pattern.both.Holds D)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → E D.d) (hA1 : CompleteRecourse D)
    (hv_bot : value P D .both ξ ≠ ⊥) (hv_top : value P D .both ξ ≠ ⊤)
    (α δ : ℝ) (R : NNReal) (hα : 0 < α) (hδ : 0 < δ)
    (hA2 : LevelBoundedWith P D .both ξ α δ R)
    (hA3 : Admissible P D .both ξ) (hX1 : Bornology.IsBounded (X1 D)) :
    ∃ L : ℝ, 0 < L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ α →
      ∀ ξ' : ℕ → Ω → E D.d, Admissible P D .both ξ' →
        inputDist P D .both ξ ξ' < ENNReal.ofReal δ →
        value P D .both ξ' ≠ ⊥ → value P D .both ξ' ≠ ⊤ →
        ∀ xbar ∈ levelSet P D .both ξ ((value P D .both ξ).toReal + ε),
          ENNReal.ofReal ((value P D .both ξ').toReal - (value P D .both ξ).toReal - ε) ≤
            ENNReal.ofReal L * (inputDist P D .both ξ ξ' +
              ∑ τ ∈ Finset.Icc 2 (D.T - 1), eLpNorm (xbar τ - P[xbar τ | sigmaGen ξ' τ]) 2 P) := by sorry

end MultistageStab.Value
