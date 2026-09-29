-- Prove2me | Theorems.Thm_FoundationsML_SVM_margin_bound_linear_hypotheses
-- name    : FoundationsML.SVM.margin_bound_linear_hypotheses
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:31:50.384322+00:00
-- url     : https://prove2.me/theorems/4da9f8c1-a2c6-48b7-8eca-9f58c9be544b
-- title:
--   Corollary 5.11 — Margin bound for norm-bounded linear hypotheses
-- statement:
--   **Statement (Corollary 5.11, p. 97, PDF p. 114).** Let $H=\{x\mapsto w\cdot x:\|w\|\le
--   \Lambda\}$ and assume $X\subseteq\{x:\|x\|\le r\}$. Fix $\rho>0$; then, for any $\delta>0$,
--   with probability at least $1-\delta$ over the choice of a sample $S$ of size $m$, the
--   following holds for any $h\in H$:
--   $$R(h) \le \hat R_{S,\rho}(h) + 2\sqrt{\frac{r^2\Lambda^2/\rho^2}{m}} +
--     \sqrt{\frac{\log(1/\delta)}{2m}}.$$
--
--   This is the concrete, dimension-free margin bound obtained by combining Theorem 5.10's
--   Rademacher-complexity bound for linear hypotheses with Theorem 5.8's general margin bound —
--   the guarantee that gives SVMs their theoretical justification.
--
--   **Formalization Note.** `[BorelSpace X]` records the measurable structure under which every
--   `x ↦ inner ℝ w x` is measurable (implicit in the book, never separately discussed); `hX`
--   is the book's population bound `X ⊆ {x : ‖x‖ ≤ r}`, stated as `∀ᵐ p ∂D, ‖p.1‖ ≤ r` (D-almost
--   every drawn point respects the bound).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 97, Corollary 5.11 (PDF p. 114)

import Mathlib
import Definitions.Def_FoundationsML_SVM_MarginGeneralizationError
import Definitions.Def_FoundationsML_SVM_EmpiricalMarginLoss

open MeasureTheory

namespace FoundationsML.SVM

/-- Corollary 5.11 (margin bound for norm-bounded linear hypotheses; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 97, PDF p. 114).
Let `H = {x ↦ w · x : ‖w‖ ≤ Λ}` and assume `X ⊆ {x : ‖x‖ ≤ r}`. Fix `ρ > 0`; then, for any
`δ > 0`, with probability at least `1 − δ` over the draw of a sample `S` of size `m`,
`R(h) ≤ R̂_{S,ρ}(h) + 2·sqrt((r²Λ²/ρ²)/m) + sqrt(log(1/δ)/(2m))` holds for all `h ∈ H`.

**Formalization Note.** `[BorelSpace X]` records that the measurable structure on `X` used to
define `MarginGeneralizationError` is the Borel one, under which every `x ↦ inner ℝ w x` is
measurable; this is implicit in the book and not separately discussed. The a.e. hypothesis
`hX` is the book's population bound `X ⊆ {x : ‖x‖ ≤ r}`. -/
theorem margin_bound_linear_hypotheses
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (r Λ : ℝ) (hr : 0 ≤ r) (hΛ : 0 ≤ Λ) (hX : ∀ᵐ p ∂D, ‖p.1‖ ≤ r)
    (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ) (m : ℕ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ w : X, ‖w‖ ≤ Λ →
        MarginGeneralizationError D (fun x => inner ℝ w x) ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) (fun x => inner ℝ w x) +
            2 * Real.sqrt (r ^ 2 * Λ ^ 2 / ρ ^ 2 / m) +
            Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.SVM
