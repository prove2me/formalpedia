-- Prove2me | Theorems.Thm_MultistageStab_Value_display_15
-- name    : MultistageStab.Value.display_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:17.33099+00:00
-- url     : https://prove2.me/theorems/1d1cb31c-384e-4d35-9486-2df32a3ba60c
-- title:
--   (15), proof of Theorem 2.1, p. 7 — v(ξ) − v(ξ̃) ≤ L(‖ξ − ξ̃‖_r + Σ_t sup_{x̃∈l_{α,t}(F(ξ̃,·))} ‖x̃_t − E[x̃_t|F_t]‖_{r′})
-- statement:
--   Work in the setting of program (1) for any of the three randomness patterns, with exponents $r, r'$. Assume (A1), $X_1$ bounded, $\xi$ admissible, $v(\xi)$ finite, and the level-boundedness of (A2) with constants $\alpha > 0$, $\delta > 0$. Then there is a constant $L > 0$ such that for every admissible $\tilde\xi$ with $\|\xi - \tilde\xi\|_r < \delta$ and $v(\tilde\xi)$ finite,
--   $$v(\xi) - v(\tilde\xi) \le L\Big( \|\xi - \tilde\xi\|_r + \sum_{t=2}^{T-1} \sup_{\tilde x \in l_{\alpha}(F(\tilde\xi,\cdot))} \big\|\tilde x_t - \mathbb E[\tilde x_t \mid \mathcal F_t]\big\|_{r'} \Big),$$
--   where $l_\alpha(F(\tilde\xi,\cdot)) = \{\tilde x \in \mathcal X(\tilde\xi) : F(\tilde\xi,\tilde x) \le v(\xi) + \alpha\}$ is the perturbed level set of (A2), with the unperturbed value $v(\xi)$ in its threshold.
--
--   This is the estimate (14) with the roles of $\xi$ and $\tilde\xi$ exchanged.
--
--   **Formalization Note** The inequality is stated in $[0,\infty]$ with its left-hand side truncated at $0$; the suprema are taken in $[0,\infty]$.
-- source:
--   Heitsch, Römisch & Strugarek, Stability of multistage stochastic programs, author manuscript (edoc.hu-berlin.de, c. 2005), p. 7, proof of Theorem 2.1, (15)

import Mathlib
import Definitions.Def_MultistageStab_Value_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultistageStab.Value

theorem display_15 (D : Data) (pat : Pattern) (hpat : pat.Holds D)
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
        ENNReal.ofReal ((value P D pat ξ).toReal - (value P D pat ξ').toReal) ≤
          ENNReal.ofReal L * (inputDist P D pat ξ ξ' +
            ∑ t ∈ Finset.Icc 2 (D.T - 1),
              ⨆ xtil ∈ levelSet P D pat ξ' ((value P D pat ξ).toReal + α),
                eLpNorm (xtil t - P[xtil t | sigmaGen ξ t]) (r' pat) P) := by sorry

end MultistageStab.Value
