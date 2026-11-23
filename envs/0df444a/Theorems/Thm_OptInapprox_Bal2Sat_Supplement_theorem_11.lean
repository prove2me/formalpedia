-- Prove2me | Theorems.Thm_OptInapprox_Bal2Sat_Supplement_theorem_11
-- name    : OptInapprox.Bal2Sat.Supplement.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:01:38.794898+00:00
-- url     : https://prove2.me/theorems/1e3b5e75-0987-4906-a3b2-faf63942a1e0
-- title:
--   Theorem 11 — UGC hardness of MAX-q-CUT: (1−ε) vs 1 − 1/q + 2ln q/q² + O(ln ln q)/q²
-- statement:
--   Assume the published Unique Games Conjecture. There are a real constant $C$ and an integer $q_0$ such that for every integer $q\ge\max(2,q_0)$ and every $\epsilon>0$ it is NP-hard to distinguish MAX-$q$-CUT instances with optimum cut fraction at least $1-\epsilon$ from those with optimum cut fraction at most
--
--   $$1-\frac1q+\frac{2\ln q}{q^2}+\frac{C\ln\ln q}{q^2}.$$
--
--   This matches the Frieze–Jerrum approximation guarantee up to the lower-order term. Hardness means polynomial-time many-one gap reductions from every NP language.
--
--   Differences from the source:
--   - reading: at most (1 − 1/q + (2 ln q)/q² + O(ln ln q)/q²)-satisfiable → ∃ C q₀, ∀ q ≥ max(2,q₀), ∀ ε>0: soundness 1 − 1/q + 2 ln q/q² + C ln ln q/q²; reason: O(·) as q→∞ with one constant uniform in q and ε; the proof (p. 34) takes q sufficiently large
--   - encoding: weighted MAX-q-CUT (Definition 13) → unit-weight lists of ordered pairs with repetition, nonempty in both promises; reason: hardness on the encodable subclass implies hardness on the source class; the empty instance has no defined fraction
--   - reading: NP-hard to distinguish → published OptInapprox.MaxCut.GapNPHard; reason: same gap-reduction convention as the published UGC
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 14, Theorem 11; proof §11, pp. 33–35

import Mathlib
import Definitions.Def_OptInapprox_Bal2Sat_Supplement_QCut

namespace OptInapprox.Bal2Sat.Supplement

theorem theorem_11 (hUGC : OptInapprox.MaxCut.UGC) :
    ∃ (C : ℝ) (q₀ : ℕ), ∀ q : ℕ, ∀ hq : 2 ≤ q, q₀ ≤ q →
      letI : NeZero q := ⟨by omega⟩
      ∀ ε : ℝ, 0 < ε →
        QCutGapHard q (1 - ε)
          (1 - 1 / (q : ℝ) + 2 * Real.log q / (q : ℝ) ^ 2 +
            C * Real.log (Real.log q) / (q : ℝ) ^ 2) := by sorry

end OptInapprox.Bal2Sat.Supplement
