-- Prove2me | Theorems.Thm_IAFTRL_proposition_D_2
-- name    : IAFTRL.proposition_D_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:50:39.742811+00:00
-- url     : https://prove2.me/theorems/379f041e-d515-4cc8-b000-824121bfbfe8
-- title:
--   Proposition D.2 — all-history adversarial guarantee
-- statement:
--   Let $\mathcal A$ be a finite action set in the unit ball of $\mathbb R^d$ ($d\ge1$) spanning $\mathbb R^d$, with $K=|\mathcal A|$. For every execution of IA-FTRL for $T\ge1$ rounds against an adaptive environment and every comparator action $u\in\mathcal A$,
--   $$
--   \mathrm{Reg}_T(u)\le\min\Big\{2T,\ 16d\log(eK)+21\sqrt{dT\log(eK)}\Big\}.
--   $$
--   Hence $\sup_{u\in\mathcal A}\mathrm{Reg}_T(u)$ obeys the same bound. This is the adversarial half of Proposition 2.1, with explicit constants.
--
--   **Formalization Note** A bound for every comparator action is the bound on the supremum, which is taken outside the expectation (Appendix J.1).
--
--   Differences from the source:
--   - encoding: $\sup_{u\in\mathcal A}\mathrm{Reg}_T(u)$ → a bound on $\mathrm{Reg}_T(u)$ for every $u\in\mathcal A$; reason: finite $\mathcal A$; same statement
--   - reading: IA-FTRL with "a fixed $\mathcal F_{t-1}$-measurable rule" for $p_t$ → every $\mathcal F_{t-1}$-measurable minimizer of (2.3); reason: p.17 leaves the rule open ("e.g., the lexicographically smallest"); the bound uses only feasibility
--   - reading: protocol $\mathbb E[Y_t\mid\mathcal F_{t-1},\theta_t,A_t]=A_t^\top\theta_t$, $A_t\sim p_t$ → action law given $\mathcal G_t$, feedback identity given $\mathcal G_t\vee\sigma(A_t)$, for the pre-action filtration $\mathcal G_t$; reason: Appendix J.1, p.204: "Enlarging the pre-action filtration to include an environment's fresh pre-action randomization does not reveal it to the learner"
--   - encoding: dimension $d$ of $\mathbb R^d$ → $d\ge1$; reason: the paper works in $\mathbb R^d$ with a spanning action set in the unit ball; only the degenerate $d=0$ is excluded
--   - encoding: paper rounds $t=1,\dots,T$ → 0-based Lean rounds $t<T$, Lean round $t$ using $\beta_{t+1}$, $q_{t+1}$, $Z_{t+1}$; reason: Lean indexing convention; same instances
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Appendix D.1.3, Proposition D.2, p.67

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_IAFTRL_regretVs

namespace IAFTRL

open Matrix MeasureTheory

/-- **Proposition D.2 (The all-history adversarial guarantee).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Proposition D.2, p.67:
"IA-FTRL satisfies, for every `T ≥ 1`,
`sup_{u∈𝒜} Reg_T(u) ≤ min{2T, 16d log(eK) + 21√(dT log(eK))}`."

For every execution of IA-FTRL for `T ≥ 1` rounds against an adaptive environment (spanning finite
action set in the unit ball of `ℝ^d`, `d ≥ 1`) and every comparator action `u`:
`Reg_T(u) ≤ min{2T, 16d log(eK) + 21√(dT log(eK))}`.

**Formalization Note.** A bound on every `Reg_T(u)` is the bound on `sup_u Reg_T(u)` (finite
`𝒜`, supremum outside the expectation, p.204). -/
theorem proposition_D_2 {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ)
    (hA : IsActionSet arms) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℕ) (hT : 1 ≤ T) (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R)
    (u : Fin K) :
    regretVs P arms T R u ≤
      min (2 * (T : ℝ)) (16 * (d : ℝ) * Real.log (Real.exp 1 * K) +
        21 * Real.sqrt ((d : ℝ) * T * Real.log (Real.exp 1 * K))) := by sorry

end IAFTRL
