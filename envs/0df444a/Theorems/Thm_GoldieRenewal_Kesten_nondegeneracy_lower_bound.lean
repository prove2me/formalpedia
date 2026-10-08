-- Prove2me | Theorems.Thm_GoldieRenewal_Kesten_nondegeneracy_lower_bound
-- name    : GoldieRenewal.Kesten.nondegeneracy_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:11:15.717974+00:00
-- url     : https://prove2.me/theorems/462443e6-41ed-416c-a4cc-87a58a96d549
-- title:
--   Proof of Theorem 4.1, p. 157 — under (4.5), t^κP(|R| > t) is bounded away from 0 for all large t
-- statement:
--   Let $(Q,M)$ have joint law $\mu$, let $M$ satisfy the conditions of Lemma 2.2 for some $\kappa>0$, let $\mathbf E|Q|^\kappa<\infty$ (4.2), and assume (4.5):
--
--   $$
--   \text{for each fixed } c\in\mathbb R,\qquad P\big(Q=(1-M)c\big)<1 .
--   $$
--
--   Let $R$ have a law solving $R\overset{\mathcal L}{=}Q+MR$ with $R$ independent of $(Q,M)$. Then there is $c>0$ such that $t^\kappa P(|R|>t)\ge c$ for all sufficiently large $t$.
--
--   This is the nontrivial half of the last assertion of Theorem 4.1: under (4.5) the tail constants satisfy $C_++C_->0$. Without (4.5), $Q=(1-M)c$ a.s. for some $c$, the constant $R\equiv c$ solves the equation, and both tails vanish.
--
--   **Formalization Note** The statement is made for every law solving the equation; by Theorem 4.1 there is exactly one.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 157, proof of Theorem 4.1, unnumbered

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Kesten_RandomDifferenceEquation

namespace GoldieRenewal.Kesten

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- **Non-degeneracy of the tails** (Goldie, *Implicit renewal theory and tails of solutions of
random equations*, Ann. Appl. Probab. 1(1) (1991), p. 157, proof of Theorem 4.1, unnumbered:
"let us assume (4.5) and prove `|t|^κP(|R| > t)` is bounded away from 0 for all large `t`").
Under the hypotheses of Theorem 4.1 and (4.5) — for each fixed `c ∈ ℝ`, `P(Q = (1 − M)c) < 1` —
let `ρ` be a law for `R` satisfying (1.1). Then there is `c > 0` with
`t^κ P(|R| > t) ≥ c` for all sufficiently large `t`.

**Formalization Note** `P(|R| > t)` is `ρ{r : |r| > t}`; as `t → ∞`, `|t| = t`. Stated for every
law solving (1.1) (unique by Theorem 4.1). -/
theorem nondegeneracy_lower_bound (κ : ℝ) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hM : GoldieRenewal.Implicit.CramerConditions κ (μ.map Prod.snd))
    (hQ : ∫⁻ p, ENNReal.ofReal (|p.1| ^ κ) ∂μ < ∞)
    (h45 : ∀ c : ℝ, μ {p | p.1 = (1 - p.2) * c} < 1)
    (ρ : ProbabilityMeasure ℝ) (hρ : rdeOperator μ (ρ : Measure ℝ) = ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in atTop, c ≤ t ^ κ * (ρ : Measure ℝ).real {r | t < |r|} := by sorry

end GoldieRenewal.Kesten
