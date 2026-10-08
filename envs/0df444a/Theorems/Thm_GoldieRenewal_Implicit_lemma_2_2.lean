-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_lemma_2_2
-- name    : GoldieRenewal.Implicit.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:57.815975+00:00
-- url     : https://prove2.me/theorems/6d6fb73c-5e9f-46ce-9c1f-65e5ed067bd4
-- title:
--   Lemma 2.2 — under (2.3)–(2.5), −∞ ≤ E log|M| < 0 and m = E|M|^κ log|M| ∈ (0, ∞)
-- statement:
--   Let $M$ be a real random variable such that, for some $\kappa>0$,
--   $$
--   \text{(2.3)}\ E|M|^\kappa = 1,\qquad \text{(2.4)}\ E|M|^\kappa\log^+|M|<\infty,
--   $$
--   and (2.5) the conditional law of $\log|M|$ given $M\neq0$ is nonarithmetic. Then
--   $$
--   \text{(2.6)}\quad -\infty\le E\log|M|<0
--   \qquad\text{and}\qquad
--   \text{(2.7)}\quad m := E|M|^\kappa\log|M|\in(0,\infty).
--   $$
--
--   Lemma 2.2 shows that the Cramér-type conditions force a negative drift of $\log|M|$ and a finite positive constant $m$; $m$ is the mean of the tilted law $\eta(du) = e^{\kappa u}P(\log|M|\in du)$ and is the normalising constant of the implicit renewal theorem.
--
--   **Formalization Note** (2.6) is stated as: $E\log^+|M|<\infty$, so that $E\log|M| = E\log^+|M| - E\log^-|M|$ is a well-defined extended real (with $\log 0=-\infty$), and this extended real is negative; the value $-\infty$ is allowed. (2.7) is stated as integrability of $|M|^\kappa\log|M|$ together with $m>0$.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 129, Lemma 2.2

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GoldieRenewal.Implicit

/-- **Lemma 2.2** (Goldie, *Implicit renewal theory and tails of solutions of random equations*,
Ann. Appl. Probab. 1(1):126–166 (1991), p. 129). Let `M` be a random variable such that, for some
`κ > 0`, (2.3) `E|M|^κ = 1`, (2.4) `E|M|^κ log⁺|M| < ∞` and (2.5) the conditional law of `log|M|`
given `M ≠ 0` is nonarithmetic. Then (2.6) `−∞ ≤ E log|M| < 0` and (2.7)
`m := E|M|^κ log|M| ∈ (0, ∞)`.

**Formalization Note** The hypotheses are `CramerConditions κ (P.map M)` (the law of `M`).
(2.6) is stated as: `E log⁺|M| < ∞` (so `E log|M| = E log⁺|M| − E log⁻|M|` is a well-defined element
of `[−∞, ∞)`, with `log 0 = −∞`), and this extended real is `< 0`; the value `−∞` is allowed, as in
the paper. (2.7) is stated as integrability of `|M|^κ log|M|` (finiteness) together with `0 < m`. -/
theorem lemma_2_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Ω → ℝ) (hM : Measurable M) (κ : ℝ) (hC : CramerConditions κ (P.map M)) :
    (logPlusMoment (P.map M) < ∞ ∧ logAbsMean (P.map M) < 0) ∧
      (Integrable (fun x : ℝ => |x| ^ κ * Real.log |x|) (P.map M) ∧
        0 < cramerMean κ (P.map M)) := by sorry

end GoldieRenewal.Implicit
