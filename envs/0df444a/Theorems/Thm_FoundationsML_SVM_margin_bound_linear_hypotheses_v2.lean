-- Prove2me | Theorems.Thm_FoundationsML_SVM_margin_bound_linear_hypotheses_v2
-- name    : FoundationsML.SVM.margin_bound_linear_hypotheses_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:19:10.196985+00:00
-- url     : https://prove2.me/theorems/88f09559-5352-4c3e-9856-ed68a44224d9
-- title:
--   Corollary 5.11 — margin bound for norm-bounded linear hypotheses ($m\ge1$, labels $\pm1$)
-- statement:
--   **Statement (Corollary 5.11, p. 97, PDF p. 114).** Let $H=\{x\mapsto w\cdot x:\|w\|\le\Lambda\}$ and assume $X\subseteq\{x:\|x\|\le r\}$; labels are in $\{-1,+1\}$. Fix $\rho>0$; then, for any $\delta\in(0,1)$, with probability at least $1-\delta$ over the choice of a sample $S$ of size $m\ge1$, the following holds for any $h\in H$:
--   $$R(h) \le \hat R_{S,\rho}(h) + 2\sqrt{\frac{r^2\Lambda^2/\rho^2}{m}} + \sqrt{\frac{\log(1/\delta)}{2m}}.$$
--
--   **Formalization Note.** The retired version allowed $m=0$, where every sample-dependent term is Lean's $x/0=0$ and the bound is false. New: $m\ge1$, $\delta\in(0,1)$ (standing conventions), and labels in $\{-1,+1\}$ $D$-almost surely (the binary setting of §5.4 required by Theorem 5.8, through which the corollary is proved). `[BorelSpace X]` records the Borel measurable structure under which every $x\mapsto\langle w,x\rangle$ is measurable (the book's standing measurability convention); the population bound $X\subseteq\{\|x\|\le r\}$ is stated $D$-almost surely.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 97, Corollary 5.11 (PDF p. 114)

import Mathlib
import Definitions.Def_FoundationsML_SVM_MarginGeneralizationError
import Definitions.Def_FoundationsML_SVM_EmpiricalMarginLoss

open MeasureTheory

namespace FoundationsML.SVM

/-- Corollary 5.11 (margin bound for norm-bounded linear hypotheses; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 97, PDF p. 114).
Let `H = {x ↦ w · x : ‖w‖ ≤ Λ}` and assume `X ⊆ {x : ‖x‖ ≤ r}`; labels are in `{−1,+1}`.
Fix `ρ > 0`; then, for any `δ > 0`, with probability at least `1 − δ` over the draw of a
sample `S` of size `m ≥ 1`, `R(h) ≤ R̂_{S,ρ}(h) + 2·sqrt((r²Λ²/ρ²)/m) + sqrt(log(1/δ)/(2m))`
holds for all `h ∈ H`.

**Formalization Note.** Replaces `margin_bound_linear_hypotheses`, which allowed `m = 0`
(every sample-dependent term is then Lean's `x / 0 = 0`). Now `m ≥ 1` and `δ ∈ (0,1)`
(standing conventions), and the labels are in `{−1,+1}` `D`-almost surely (`hDy`, the binary
classification setting of §5.4 that Theorem 5.8, through which this corollary is proved,
requires). `[BorelSpace X]` records that the measurable structure on `X` is the Borel one,
under which every `x ↦ ⟪w, x⟫` is measurable (the book's standing measurability convention);
`hX` is the book's population bound `X ⊆ {x : ‖x‖ ≤ r}` stated `D`-almost surely. -/
theorem margin_bound_linear_hypotheses_v2
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (hDy : ∀ᵐ p ∂D, p.2 = 1 ∨ p.2 = -1)
    (r Λ : ℝ) (hr : 0 ≤ r) (hΛ : 0 ≤ Λ) (hX : ∀ᵐ p ∂D, ‖p.1‖ ≤ r)
    (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ) (hm : 0 < m) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ w : X, ‖w‖ ≤ Λ →
        MarginGeneralizationError D (fun x => inner ℝ w x) ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) (fun x => inner ℝ w x) +
            2 * Real.sqrt (r ^ 2 * Λ ^ 2 / ρ ^ 2 / m) +
            Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.SVM
