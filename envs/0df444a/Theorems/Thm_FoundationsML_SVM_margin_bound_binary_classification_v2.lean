-- Prove2me | Theorems.Thm_FoundationsML_SVM_margin_bound_binary_classification_v2
-- name    : FoundationsML.SVM.margin_bound_binary_classification_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:19:20.620074+00:00
-- url     : https://prove2.me/theorems/6baebbce-09a8-41ea-8daa-87af4ae14098
-- title:
--   Theorem 5.8 — margin bound for binary classification (goal; labels $\pm1$, $m\ge1$)
-- statement:
--   **Statement (Theorem 5.8, p. 93, PDF p. 110).** Let $H$ be a set of real-valued (measurable) functions mapping into a bounded interval, and $D$ a distribution over $X\times\{-1,+1\}$. Fix $\rho>0$; then, for any $\delta\in(0,1)$, with probability at least $1-\delta$ over an i.i.d. sample of size $m\ge1$, each of the following holds for all $h\in H$:
--   $$R(h) \le \hat R_{S,\rho}(h) + \frac2\rho R_m(H) + \sqrt{\frac{\log(1/\delta)}{2m}}, \qquad (5.39)$$
--   $$R(h) \le \hat R_{S,\rho}(h) + \frac2\rho \hat R_S(H) + 3\sqrt{\frac{\log(2/\delta)}{2m}}. \qquad (5.40)$$
--   Each inequality holds with probability at least $1-\delta$.
--
--   **Formalization Note.** The retired version allowed $m=0$, where every sample-dependent term is Lean's $x/0=0$ and the bound is false. Changes: (i) $m\ge1$, $\delta\in(0,1)$ (standing conventions); (ii) the labels are in $\{-1,+1\}$ $D$-almost surely — the binary classification setting of §5.4, needed for the proof's identity $R_m(\{(x,y)\mapsto yh(x)\})=R_m(H)$; for real labels of large magnitude the bound is false (e.g. $y\equiv100$, $H=\{-1+2\mathbf 1_F : F\text{ finite}\}$, $\rho=100$); (iii) $H$ maps into a bounded interval $[a,b]$ — Definition 3.1's standing domain for $R_m(H)$ (for unbounded $H$ the book's bound is trivially $+\infty$ while Lean's real supremum would be junk); (iv) the corrected `EmpiricalRademacherComplexity`/`RademacherComplexity` (`_v2`, supremum over exactly $H$) are used; (v) the book's footnote 3 (p. 30), measurability of the supremum defining $\hat R_S(H)$, is explicit (`hHsup`), without which the Bochner integral $R_m(H)$ would be $0$; (vi) the two inequalities are each asserted with probability $\ge1-\delta$, as the book proves them — the retired version demanded both inside a single $1-\delta$ event, which the proof does not establish. $D.\mathrm{map}\,\mathrm{Prod.fst}$ is the marginal of $D$ on $X$; the vacuous hypothesis `Measurable Prod.fst` was dropped.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 93, Theorem 5.8 (PDF p. 110)

import Mathlib
import Definitions.Def_FoundationsML_SVM_MarginGeneralizationError
import Definitions.Def_FoundationsML_SVM_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_SVM_RademacherComplexity_v2

open MeasureTheory

namespace FoundationsML.SVM

/-- Theorem 5.8 (margin bound for binary classification; Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 93, PDF p. 110). Let `H` be a
set of real-valued functions (bounded, as Definition 3.1 requires) and `D` a distribution over
`X × {−1,+1}`. Fix `ρ > 0`; then, for any `δ > 0`, with probability at least `1 − δ` over an
i.i.d. sample of size `m ≥ 1`, each of the following holds for all `h ∈ H`:
`R(h) ≤ R̂_{S,ρ}(h) + (2/ρ) R_m(H) + sqrt(log(1/δ)/(2m))`   (5.39)
and `R(h) ≤ R̂_{S,ρ}(h) + (2/ρ) R̂_S(H) + 3·sqrt(log(2/δ)/(2m))`   (5.40).

**Formalization Note.** Replaces `margin_bound_binary_classification`, which allowed `m = 0`
(every sample-dependent term is then Lean's `x / 0 = 0`). Changes: `m ≥ 1`, `δ ∈ (0,1)`
(standing conventions); the labels are in `{−1,+1}` `D`-almost surely (`hDy`, the binary
classification setting of §5.4 — the proof's identity `R_m({(x,y) ↦ y h(x)}) = R_m(H)` needs
`y ∈ {−1,+1}`, and the bound is false for real labels of large magnitude); `H` maps into a
bounded interval (`hHb`, Definition 3.1's domain for `R_m(H)`); the corrected
`EmpiricalRademacherComplexity`/`RademacherComplexity` (`_v2`, supremum over exactly `H`) are
used; the book's footnote 3 (p. 30) that the supremum defining `R̂_S(H)` is measurable is made
explicit (`hHsup`, needed for `R_m(H)` to be the book's expectation rather than Lean's junk
`0`); and the two inequalities are each asserted with probability at least `1 − δ`, as the
book proves them (the retired version demanded both inside one `1 − δ` event, which the proof
does not establish). `D.map Prod.fst` is the marginal of `D` on `X`. -/
theorem margin_bound_binary_classification_v2
    {X : Type*} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (hDy : ∀ᵐ p ∂D, p.2 = 1 ∨ p.2 = -1)
    (H : Set (X → ℝ)) (hHb : ∃ a b : ℝ, ∀ h ∈ H, ∀ x, h x ∈ Set.Icc a b)
    (hHmeas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (hm : 0 < m)
    (hHsup : Measurable (fun S : Fin m → X => EmpiricalRademacherComplexity H S))
    (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        MarginGeneralizationError D h ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) h +
            (2 / ρ) * RademacherComplexity (D.map Prod.fst) H m +
            Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal ∧
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        MarginGeneralizationError D h ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) h +
            (2 / ρ) * EmpiricalRademacherComplexity H (fun i => (S i).1) +
            3 * Real.sqrt (Real.log (2 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.SVM
