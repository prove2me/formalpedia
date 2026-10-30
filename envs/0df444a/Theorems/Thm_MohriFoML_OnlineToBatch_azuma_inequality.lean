-- Prove2me | Theorems.Thm_MohriFoML_OnlineToBatch_azuma_inequality
-- name    : MohriFoML.OnlineToBatch.azuma_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:07:55.791068+00:00
-- url     : https://prove2.me/theorems/9a3f896b-6bce-4238-869f-161f2f19af35
-- title:
--   Theorem D.7 — Azuma's inequality, both tails (corrected: $\mathbb{E}[V_1] = 0$ added)
-- statement:
--   Let $(\Omega, \mathcal{F}, P)$ be a probability space with a filtration $\mathcal{F}_1 \subseteq \mathcal{F}_2 \subseteq \cdots$ (for instance $\mathcal{F}_i = \sigma(X_1, \dots, X_i)$ for random variables $X_1, X_2, \dots$). Let $V_1, V_2, \dots$ be integrable real random variables forming a **martingale difference sequence**: each $V_i$ is $\mathcal{F}_i$-measurable and
--
--   $$
--   \mathbb{E}[V_1] = 0, \qquad \mathbb{E}[V_{i+1} \mid \mathcal{F}_i] = 0 \quad (i \ge 1).
--   $$
--
--   Assume that for every $i \ge 1$ there are a constant $c_i \ge 0$ and a random variable $Z_i$, which is $\mathcal{F}_{i-1}$-measurable ($Z_1$ a constant), such that
--
--   $$
--   Z_i \le V_i \le Z_i + c_i .
--   $$
--
--   Then for every $\epsilon > 0$ and every $m$,
--
--   $$
--   P\Big[\sum_{i=1}^m V_i \ge \epsilon\Big] \le \exp\Big(\frac{-2\epsilon^2}{\sum_{i=1}^m c_i^2}\Big), \qquad P\Big[\sum_{i=1}^m V_i \le -\epsilon\Big] \le \exp\Big(\frac{-2\epsilon^2}{\sum_{i=1}^m c_i^2}\Big).
--   $$
--
--   Azuma's inequality extends Hoeffding's inequality from independent summands to bounded martingale differences. In Section 8.4 it is applied to $V_t = R(h_t) - L(h_t(x_t), y_t)$, which gives Lemma 8.14.
--
--   **Formalization Note** Indices are 0-based in Lean (`V i` is the book's $V_{i+1}$). When $\sum c_i^2 = 0$ the right-hand side is read as $\exp(0) = 1$ (Lean's convention $x / 0 = 0$); there the bound holds trivially.
--
--   Differences from the source:
--   - correction: V_1 need not be centred (Definition D.5 imposes E[V_{i+1} | X_1, …, X_i] = 0 only for i > 0) → E[V_1] = 0 added; reason: as printed the theorem is false: m = 1, V_1 ≡ 1, Z_1 ≡ 0 (a function of no variables), c_1 = 1, ε = 1 satisfy every assumption, yet P[V_1 ≥ 1] = 1 > e^{−2}; E[V_1] = 0 is the i = 0 case of (D.9), used by the book's proof in its last iteration
--   - generalization: V_i a function of X_1, …, X_i and Z_i a function of X_1, …, X_{i−1} → V_i measurable for F_i and Z_{i+1} measurable for F_i, for an arbitrary filtration F; reason: the natural filtration F_i = σ(X_1, …, X_i) is one instance, so the statement specializes to the book's
--   - encoding: martingale difference sequence → each V_i integrable; reason: the conditional expectations in (D.9) are defined only then (otherwise Lean's junk value 0 would satisfy (D.9) vacuously)
--   - encoding: exp(−2ε²/Σ c_i²) with Σ c_i² = 0 (undefined) → exp(0) = 1; reason: Lean's x / 0 = 0; the bound is then trivially true and no meaningful instance changes
--   - encoding: V_i, Z_i, c_i and Σ_{i=1}^m for i = 1, 2, … → V i, Z i, c i for i = 0, 1, … and Σ over Finset.range m; reason: Lean convention (0-based index, Lean's i is the book's i + 1); same instances
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 441 (PDF p. 458), Appendix D §D.6, Definition D.5 (D.9) and Theorem D.7, (D.12)–(D.14)

import Mathlib

namespace MohriFoML.OnlineToBatch

open MeasureTheory ProbabilityTheory

/-- **Theorem D.7: Azuma's inequality (corrected: `E[V_1] = 0` added).**
Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018,
Appendix D, §D.6, p. 441 (PDF p. 458), Definition D.5 (martingale difference, (D.9)) and
Theorem D.7, inequalities (D.12)–(D.14).

Let `V_1, V_2, …` be a martingale difference sequence with respect to `X_1, X_2, …` (each `V_i` a
function of `X_1, …, X_i`, and `E[V_{i+1} | X_1, …, X_i] = 0`), with moreover `E[V_1] = 0`. Assume
that for every `i` there are a constant `c_i ≥ 0` and a random variable `Z_i`, a function of
`X_1, …, X_{i−1}`, with `Z_i ≤ V_i ≤ Z_i + c_i`. Then for all `ε > 0` and all `m`,
`P[∑_{i=1}^m V_i ≥ ε] ≤ exp(−2ε² / ∑_{i=1}^m c_i²)` and
`P[∑_{i=1}^m V_i ≤ −ε] ≤ exp(−2ε² / ∑_{i=1}^m c_i²)`.

**Formalization Note.** Indices are 0-based: Lean's `V i`, `Z i`, `c i` are the book's `V_{i+1}`,
`Z_{i+1}`, `c_{i+1}`, and `∑ i ∈ Finset.range m` is the book's `∑_{i=1}^m`. "A function of
`X_1, …, X_i`" is measurability with respect to a filtration `ℱ` (the natural filtration of the
`X_i` is one instance): `V i` is `ℱ i`-measurable, `Z (i+1)` is `ℱ i`-measurable, and `Z 0`
(the book's `Z_1`, a function of no variables) is a constant. Each `V i` is integrable, so the
conditional expectations in (D.9) are the genuine ones. The hypothesis `∫ V 0 = 0` is a
correction: as printed (Definition D.5 only centres `V_{i+1}` for `i > 0`) the theorem is false,
e.g. `m = 1`, `V_1 ≡ 1`, `Z_1 ≡ 0`, `c_1 = 1`, `ε = 1` gives `P[V_1 ≥ 1] = 1 > e^{−2}`. When
`∑ c_i² = 0` Lean's `x / 0 = 0` makes the bound `exp 0 = 1`, which holds trivially. -/
theorem azuma_inequality {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (V Z : ℕ → Ω → ℝ) (c : ℕ → ℝ)
    (hV_adapted : StronglyAdapted ℱ V)
    (hV_int : ∀ i, Integrable (V i) μ)
    (hV_zero : ∫ ω, V 0 ω ∂μ = 0)
    (hV_mds : ∀ i, μ[V (i + 1) | ℱ i] =ᵐ[μ] 0)
    (hZ_zero : ∃ z₀ : ℝ, ∀ ω, Z 0 ω = z₀)
    (hZ_pred : ∀ i, StronglyMeasurable[ℱ i] (Z (i + 1)))
    (hc : ∀ i, 0 ≤ c i)
    (hlow : ∀ i ω, Z i ω ≤ V i ω) (hup : ∀ i ω, V i ω ≤ Z i ω + c i) :
    ∀ ε : ℝ, 0 < ε → ∀ m : ℕ,
      μ.real {ω | ε ≤ ∑ i ∈ Finset.range m, V i ω}
          ≤ Real.exp (-2 * ε ^ 2 / ∑ i ∈ Finset.range m, c i ^ 2) ∧
        μ.real {ω | ∑ i ∈ Finset.range m, V i ω ≤ -ε}
          ≤ Real.exp (-2 * ε ^ 2 / ∑ i ∈ Finset.range m, c i ^ 2) := by sorry

end MohriFoML.OnlineToBatch
