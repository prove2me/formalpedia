-- Prove2me | Theorems.Thm_MultistageStab_Value_case_rhs_random
-- name    : MultistageStab.Value.case_rhs_random
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:13.816016+00:00
-- url     : https://prove2.me/theorems/6331e46b-278a-4a19-9041-bdaffe0c9472
-- title:
--   Proof of Theorem 2.1, p. 6, case "only right-hand sides random" — v(ξ̃) − v(ξ) ≤ L(‖ξ − ξ̃‖_1 + Σ‖x̄_τ − E[x̄_τ|F̃_τ]‖_1) + ε
-- statement:
--   Work in the setting of program (1) when only the right-hand sides are random ($b_t$ deterministic, $r = r' = 1$). Assume (A1), $X_1$ bounded, $\xi$ admissible, $v(\xi)$ finite, and the level-boundedness of (A2) with constants $\alpha > 0$, $\delta > 0$. Then there is a constant $L > 0$ such that for every $\varepsilon \in (0,\alpha]$, every admissible $\tilde\xi$ with $\|\tilde\xi - \xi\|_1 < \delta$ and $v(\tilde\xi)$ finite, and every $\bar x$ in the level set $l_\varepsilon(F(\xi,\cdot)) = \{x \in \mathcal X(\xi) : F(\xi,x) \le v(\xi) + \varepsilon\}$,
--   $$v(\tilde\xi) - v(\xi) \le L\Big( \|\xi - \tilde\xi\|_1 + \sum_{\tau=2}^{T-1} \big\|\bar x_\tau - \mathbb E[\bar x_\tau \mid \tilde{\mathcal F}_\tau]\big\|_1 \Big) + \varepsilon .$$
--
--   This is the first of the three case estimates in the proof of Theorem 2.1.
--
--   **Formalization Note** The inequality is stated in $[0,\infty]$ as $\max\{v(\tilde\xi) - v(\xi) - \varepsilon, 0\} \le L(\dots)$, which is equivalent to the real inequality whenever the right-hand side is finite. The paper's printed constant $\hat L T$ is kept existential, as the paper's later steps do.
-- source:
--   Heitsch, Römisch & Strugarek, Stability of multistage stochastic programs, author manuscript (edoc.hu-berlin.de, c. 2005), pp. 5–6, proof of Theorem 2.1, case "only right-hand sides being random"

import Mathlib
import Definitions.Def_MultistageStab_Value_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultistageStab.Value

theorem case_rhs_random (D : Data) (hpat : Pattern.rhs.Holds D)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → E D.d) (hA1 : CompleteRecourse D)
    (hv_bot : value P D .rhs ξ ≠ ⊥) (hv_top : value P D .rhs ξ ≠ ⊤)
    (α δ : ℝ) (R : NNReal) (hα : 0 < α) (hδ : 0 < δ)
    (hA2 : LevelBoundedWith P D .rhs ξ α δ R)
    (hA3 : Admissible P D .rhs ξ) (hX1 : Bornology.IsBounded (X1 D)) :
    ∃ L : ℝ, 0 < L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ α →
      ∀ ξ' : ℕ → Ω → E D.d, Admissible P D .rhs ξ' →
        inputDist P D .rhs ξ ξ' < ENNReal.ofReal δ →
        value P D .rhs ξ' ≠ ⊥ → value P D .rhs ξ' ≠ ⊤ →
        ∀ xbar ∈ levelSet P D .rhs ξ ((value P D .rhs ξ).toReal + ε),
          ENNReal.ofReal ((value P D .rhs ξ').toReal - (value P D .rhs ξ).toReal - ε) ≤
            ENNReal.ofReal L * (inputDist P D .rhs ξ ξ' +
              ∑ τ ∈ Finset.Icc 2 (D.T - 1), eLpNorm (xbar τ - P[xbar τ | sigmaGen ξ' τ]) 1 P) := by sorry

end MultistageStab.Value
