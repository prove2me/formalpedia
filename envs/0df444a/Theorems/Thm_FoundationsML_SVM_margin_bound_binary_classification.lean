-- Prove2me | Theorems.Thm_FoundationsML_SVM_margin_bound_binary_classification
-- name    : FoundationsML.SVM.margin_bound_binary_classification
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:32:33.530408+00:00
-- url     : https://prove2.me/theorems/6f2e8ca2-9f42-45b3-a2a2-a765ef95ec55
-- title:
--   Theorem 5.8 — Margin bound for binary classification (goal)
-- statement:
--   **Statement (Theorem 5.8, p. 93, PDF p. 110).** Let $H$ be a set of real-valued functions.
--   Fix $\rho>0$; then, for any $\delta>0$, with probability at least $1-\delta$, each of the
--   following holds for all $h\in H$:
--   $$R(h) \le \hat R_{S,\rho}(h) + \frac2\rho R_m(H) + \sqrt{\frac{\log(1/\delta)}{2m}}$$
--   $$R(h) \le \hat R_{S,\rho}(h) + \frac2\rho \hat R_S(H) + 3\sqrt{\frac{\log(2/\delta)}{2m}}.$$
--
--   This is the chapter's capstone general margin-based generalization bound: it justifies
--   SVMs and every other large-margin algorithm by trading zero-one loss for the $\rho$-margin
--   loss (a stricter, Lipschitz-surrogate loss), then applying Theorem 3.3's Rademacher bound
--   together with Talagrand's lemma (Lemma 5.7) to the $1/\rho$-Lipschitz margin-loss
--   composition.
--
--   **Formalization Note.** `D.map Prod.fst` is the marginal of `D` on `X`, used as the sample
--   distribution for `R_m(H)` (Definition 3.2); the statement uses `H`'s own Rademacher
--   complexity (not that of the lifted class $\{(x,y)\mapsto y\,h(x):h\in H\}$), matching the
--   book's final form (the proof shows the two coincide because $y\in\{-1,+1\}$; only the
--   theorem's statement, not its proof, is drafted here). Both inequalities are asserted on the
--   same sample `S` simultaneously, matching "each of the following holds."
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 93, Theorem 5.8 (PDF p. 110)

import Mathlib
import Definitions.Def_FoundationsML_SVM_MarginGeneralizationError
import Definitions.Def_FoundationsML_SVM_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_SVM_RademacherComplexity

open MeasureTheory

namespace FoundationsML.SVM

/-- Theorem 5.8 (margin bound for binary classification; Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 93, PDF p. 110). Let `H` be a
set of real-valued functions. Fix `ρ > 0`; then, for any `δ > 0`, with probability at least
`1 − δ`, each of the following holds for all `h ∈ H`:
`R(h) ≤ R̂_{S,ρ}(h) + (2/ρ) R_m(H) + sqrt(log(1/δ)/(2m))` and
`R(h) ≤ R̂_{S,ρ}(h) + (2/ρ) R̂_S(H) + 3·sqrt(log(2/δ)/(2m))`.

**Formalization Note.** `D.map Prod.fst` is the marginal of `D` on `X`, used as the sample
distribution for `R_m(H)` (Definition 3.2); `H`'s own Rademacher complexity, not that of the
lifted class `{(x,y) ↦ y h(x) : h ∈ H}`, matches the book's final statement (the proof shows
the two coincide because `y ∈ {−1,+1}`, which is not re-derived here since only the theorem's
statement, not its proof, is drafted). Both inequalities are asserted to hold simultaneously
on the same sample `S`, as the book's "each of the following holds" states. -/
theorem margin_bound_binary_classification
    {X : Type*} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (hDfst : Measurable (Prod.fst : X × ℝ → X))
    (H : Set (X → ℝ)) (hHmeas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        (MarginGeneralizationError D h ≤
           EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) h +
             (2 / ρ) * RademacherComplexity (D.map Prod.fst) H m +
             Real.sqrt (Real.log (1 / δ) / (2 * m))) ∧
        (MarginGeneralizationError D h ≤
           EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) h +
             (2 / ρ) * EmpiricalRademacherComplexity H (fun i => (S i).1) +
             3 * Real.sqrt (Real.log (2 / δ) / (2 * m)))}).toReal := by sorry

end FoundationsML.SVM
