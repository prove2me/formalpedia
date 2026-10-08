-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_eq_9_12_9_13
-- name    : GoldieRenewal.Implicit.eq_9_12_9_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:17.506984+00:00
-- url     : https://prove2.me/theorems/abdb92a4-bcdc-4c19-b42a-f356453f4dc3
-- title:
--   (9.11)–(9.13), p. 147 — in Case 2a the law η = pη₊ + Σ q²pⁿ⁻²η₋⁽²⁾∗η₊⁽ⁿ⁻²⁾ has mean 2m and is nonarithmetic
-- statement:
--   Let $M$ satisfy the conditions of Lemma 2.2 with $P(M>0)>0$ and $P(M<0)>0$. With $p, q, \eta_+, \eta_-$ as on p. 146 (see the definition file), the measure
--   $$
--   \eta = p\eta_+ + \sum_{n=2}^\infty q^2p^{n-2}\,\eta_-^{(2)}*\eta_+^{(n-2)} \tag{9.11}
--   $$
--   is a probability law on $\mathbb R$, it has a finite mean, and
--   $$
--   \text{(9.12)}\quad\int_{\mathbb R}y\,\eta(dy) = 2m,\qquad\text{(9.13)}\quad\eta\text{ is nonarithmetic},
--   $$
--   where $m = E|M|^\kappa\log|M|$.
--
--   These are the properties that let renewal theory be applied in Case 2a, where $\log|\Pi_n|$ is a Markov-modulated walk: $\eta$ is the step law of the walk observed at the times the sign of $\Pi_n$ is $+1$.
--
--   **Formalization Note** $\eta$ is defined by the right-hand side of (9.11); the paper's identification of $\eta$ as the law of $Y_1+\dots+Y_{N_1^{(+)}}$ is not part of the statement.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, §9, proof of Theorem 2.3, Case 2a, (9.11)–(9.13), p. 147 (notation p. 146)

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Implicit_RenewalMeasures
open MeasureTheory ProbabilityTheory

namespace GoldieRenewal.Implicit

/-- **(9.11)–(9.13)** (Goldie 1991, Ann. Appl. Probab. 1(1), §9, proof of Theorem 2.3, Case 2a,
p. 147). Suppose `M` satisfies the conditions of Lemma 2.2, `P(M > 0) > 0` and `P(M < 0) > 0`.
With `p := E 1_{M>0}|M|^κ`, `q := E 1_{M<0}|M|^κ`, `η₊(dy) := P̃(M > 0, log|M| ∈ dy)/p`,
`η₋(dy) := P̃(M < 0, log|M| ∈ dy)/q` (p. 146, where `P̃(M ∈ dy) := |y|^κ P(M ∈ dy)`), the measure
`η = p η₊ + Σ_{n=2}^∞ q² p^{n−2} η₋^{(2)} ∗ η₊^{(n−2)}` of (9.11) is a probability law on `ℝ` with
(9.12) `∫_ℝ y η(dy) = 2m` and (9.13) `η` nonarithmetic.

**Formalization Note** `η` is *defined* by the right-hand side of (9.11) (`etaCase2`), so the
paper's identification of `η` as the law of `Y₁ + ⋯ + Y_{N₁^{(+)}}` is not part of the statement.
That `η` is a probability law is how the paper introduces it ("Let `η` be the law of …") and is
stated explicitly. (9.12) includes integrability of `y ↦ y` (the paper's mean is finite). `m` is
`cramerMean κ (P.map M)` (2.7). -/
theorem eq_9_12_9_13 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Ω → ℝ) (hM : Measurable M) (κ : ℝ) (hC : CramerConditions κ (P.map M))
    (hpos : 0 < P {ω | 0 < M ω}) (hneg : 0 < P {ω | M ω < 0}) :
    IsProbabilityMeasure (etaCase2 κ (P.map M)) ∧
      Integrable (fun y : ℝ => y) (etaCase2 κ (P.map M)) ∧
      ∫ y, y ∂(etaCase2 κ (P.map M)) = 2 * cramerMean κ (P.map M) ∧
      ¬ IsArithmetic (etaCase2 κ (P.map M)) := by sorry

end GoldieRenewal.Implicit
