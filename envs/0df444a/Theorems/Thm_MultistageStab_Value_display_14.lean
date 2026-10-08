-- Prove2me | Theorems.Thm_MultistageStab_Value_display_14
-- name    : MultistageStab.Value.display_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:27.04235+00:00
-- url     : https://prove2.me/theorems/f9dc74bf-5909-43a5-880f-89fcfba110e5
-- title:
--   (14), proof of Theorem 2.1, p. 7 — v(ξ̃) − v(ξ) ≤ L(‖ξ − ξ̃‖_r + Σ_t sup_{x̄∈l_{α,t}(F(ξ,·))} ‖x̄_t − E[x̄_t|F̃_t]‖_{r′})
-- statement:
--   Work in the setting of program (1) for any of the three randomness patterns, with exponents $r, r'$. Assume (A1), $X_1$ bounded, $\xi$ admissible, $v(\xi)$ finite, and the level-boundedness of (A2) with constants $\alpha > 0$, $\delta > 0$. Then there is a constant $L > 0$ such that for every admissible $\tilde\xi$ with $\|\xi - \tilde\xi\|_r < \delta$ and $v(\tilde\xi)$ finite,
--   $$v(\tilde\xi) - v(\xi) \le L\Big( \|\xi - \tilde\xi\|_r + \sum_{t=2}^{T-1} \sup_{\bar x \in l_{\alpha}(F(\xi,\cdot))} \big\|\bar x_t - \mathbb E[\bar x_t \mid \tilde{\mathcal F}_t]\big\|_{r'} \Big),$$
--   where $l_\alpha(F(\xi,\cdot)) = \{x \in \mathcal X(\xi) : F(\xi,x) \le v(\xi) + \alpha\}$.
--
--   This is the one-sided estimate of the optimal values, common to all three patterns; together with the symmetric estimate (15) it gives Theorem 2.1.
--
--   **Formalization Note** The inequality is stated in $[0,\infty]$ with its left-hand side truncated at $0$; the suprema are taken in $[0,\infty]$.
-- source:
--   Heitsch, Römisch & Strugarek, Stability of multistage stochastic programs, author manuscript (edoc.hu-berlin.de, c. 2005), p. 7, proof of Theorem 2.1, (14)

import Mathlib
import Definitions.Def_MultistageStab_Value_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultistageStab.Value

theorem display_14 (D : Data) (pat : Pattern) (hpat : pat.Holds D)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → E D.d) (hA1 : CompleteRecourse D)
    (hv_bot : value P D pat ξ ≠ ⊥) (hv_top : value P D pat ξ ≠ ⊤)
    (α δ : ℝ) (R : NNReal) (hα : 0 < α) (hδ : 0 < δ)
    (hA2 : LevelBoundedWith P D pat ξ α δ R)
    (hA3 : Admissible P D pat ξ) (hX1 : Bornology.IsBounded (X1 D)) :
    ∃ L : ℝ, 0 < L ∧
      ∀ ξ' : ℕ → Ω → E D.d, Admissible P D pat ξ' →
        inputDist P D pat ξ ξ' < ENNReal.ofReal δ →
        value P D pat ξ' ≠ ⊥ → value P D pat ξ' ≠ ⊤ →
        ENNReal.ofReal ((value P D pat ξ').toReal - (value P D pat ξ).toReal) ≤
          ENNReal.ofReal L * (inputDist P D pat ξ ξ' +
            ∑ t ∈ Finset.Icc 2 (D.T - 1),
              ⨆ xbar ∈ levelSet P D pat ξ ((value P D pat ξ).toReal + α),
                eLpNorm (xbar t - P[xbar t | sigmaGen ξ' t]) (r' pat) P) := by sorry

end MultistageStab.Value
