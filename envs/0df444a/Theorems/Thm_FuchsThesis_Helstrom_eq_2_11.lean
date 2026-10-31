-- Prove2me | Theorems.Thm_FuchsThesis_Helstrom_eq_2_11
-- name    : FuchsThesis.Helstrom.eq_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:55:30.228315+00:00
-- url     : https://prove2.me/theorems/fdb09e4d-80b8-4861-bd47-80f223d3a133
-- title:
--   Eq. (2.11) — Bayes' decision function has error $\sum_b \min\{\pi_0p_0(b),\pi_1p_1(b)\}$, and every other decision function is strictly worse
-- statement:
--   Let $p_0, p_1$ be probability distributions on the outcomes $b = 1, \dots, n$, and let $\pi_0, \pi_1 \ge 0$ with $\pi_0 + \pi_1 = 1$ be the prior probabilities that the sample is drawn from $p_0$ or from $p_1$. A decision function is any $\delta : \{1,\dots,n\} \to \{0,1\}$; its probability of error is
--
--   $$
--   P_e(\delta) = \pi_0 \sum_{b=1}^n \delta(b)\,p_0(b) + \pi_1 \sum_{b=1}^n [1-\delta(b)]\,p_1(b).
--   $$
--
--   A Bayes decision function $\delta_B$ chooses $\delta_B(b) = 0$ when $\pi_0p_0(b) > \pi_1p_1(b)$, $\delta_B(b) = 1$ when $\pi_1p_1(b) > \pi_0p_0(b)$, and anything on ties. Then
--
--   1. every Bayes decision function has error probability
--   $$
--   P_e(\delta_B) = \sum_{b=1}^n \min\{\pi_0p_0(b), \pi_1p_1(b)\};
--   $$
--   2. every decision function $\delta$ that is not a Bayes decision function has $P_e(\delta) > \sum_{b=1}^n \min\{\pi_0p_0(b), \pi_1p_1(b)\}$ (2.9).
--
--   This is the classical formula whose summand, with $p_i(b) = \mathrm{tr}(\hat\rho_i\hat E_b)$, is minimized over measurements in the quantum error probability (3.9).
--
--   Differences from the source:
--   - encoding: outcomes $b = 1,\dots,n$ and $\delta : \{1,\dots,n\}\to\{0,1\}$ → `Fin n` and `δ : Fin n → Fin 2` read in $\mathbb R$; reason: Lean convention, same functions.
--   - encoding: $P_e(\delta)$ defined by (2.3) as $\pi_0 P(\delta=1|0) + \pi_1 P(\delta=0|1)$ → the explicit sum (2.7); reason: (2.7) is the source's own rewriting of (2.3), same values.
--   - reading: $P_e(\delta) > P_e(\delta_B)$ "for any decision function $\delta$ other than Bayes'" (2.9), with $\delta_B$ "anything" on ties → clause 1 for every Bayes decision function (any choice on ties) and clause 2 for every $\delta$ that is not a Bayes decision function; reason: a $\delta$ differing from a fixed $\delta_B$ only on ties has the same error by (2.8), so "other than Bayes'" can only mean this.
--   - reading: the chain (2.10)–(2.11) through the posteriors $p(i|b)$ → only its end (2.11); reason: (2.10) is a step of the computation, and the posterior (2.4) is undefined when $p(b) = 0$.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (2.11), p.15 (PDF p.24); (2.2)–(2.9), p.14 (PDF p.23)

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsProbDist

namespace FuchsThesis.Helstrom

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (2.11), p.15 (PDF p.24), with the decision functions (2.2), the
error (2.7), Bayes' decision function (2.6) and its optimality (2.9), p.14 (PDF p.23): for
probability distributions `p₀, p₁` on `n` outcomes and priors `π₀, π₁`, every Bayes decision
function `δ_B` has error probability `P_e(δ_B) = ∑_b min{π₀p₀(b), π₁p₁(b)}`, and every decision
function `δ` that is not a Bayes decision function has a strictly larger one (2.9).

**Formalization Note.** Outcomes `b = 1, …, n` are `Fin n`; a decision function
`δ : {1,…,n} → {0,1}` is `δ : Fin n → Fin 2`, read in `ℝ` through `ℕ`. The error of `δ` is the
source's expression (2.7), `π₀ ∑_b δ(b)p₀(b) + π₁ ∑_b [1 − δ(b)]p₁(b)`. A Bayes decision function is
any `δ` with `δ(b) = 0` when `π₀p₀(b) > π₁p₁(b)` and `δ(b) = 1` when `π₁p₁(b) > π₀p₀(b)`
(arbitrary on ties), as in (2.6). The source's "any decision function `δ` other than Bayes'" in
(2.9) is `δ` not of this form: a `δ` differing from a fixed `δ_B` only on ties has the same error
by (2.8). -/
theorem eq_2_11 {n : ℕ} (π0 π1 : ℝ) (hπ0 : 0 ≤ π0) (hπ1 : 0 ≤ π1) (hπ : π0 + π1 = 1)
    (p0 p1 : Fin n → ℝ) (hp0 : FuchsVdGraaf.IsProbDist p0) (hp1 : FuchsVdGraaf.IsProbDist p1) :
    (∀ δ : Fin n → Fin 2,
        (∀ b, π1 * p1 b < π0 * p0 b → δ b = 0) →
        (∀ b, π0 * p0 b < π1 * p1 b → δ b = 1) →
        π0 * ∑ b, ((δ b : ℕ) : ℝ) * p0 b + π1 * ∑ b, (1 - ((δ b : ℕ) : ℝ)) * p1 b =
          ∑ b, min (π0 * p0 b) (π1 * p1 b)) ∧
      ∀ δ : Fin n → Fin 2,
        ¬ ((∀ b, π1 * p1 b < π0 * p0 b → δ b = 0) ∧ (∀ b, π0 * p0 b < π1 * p1 b → δ b = 1)) →
        ∑ b, min (π0 * p0 b) (π1 * p1 b) <
          π0 * ∑ b, ((δ b : ℕ) : ℝ) * p0 b + π1 * ∑ b, (1 - ((δ b : ℕ) : ℝ)) * p1 b := by sorry

end FuchsThesis.Helstrom
