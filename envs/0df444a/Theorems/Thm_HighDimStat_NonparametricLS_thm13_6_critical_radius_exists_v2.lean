-- Prove2me | Theorems.Thm_HighDimStat_NonparametricLS_thm13_6_critical_radius_exists_v2
-- name    : HighDimStat.NonparametricLS.thm13_6_critical_radius_exists_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:20:10.162557+00:00
-- url     : https://prove2.me/theorems/a0378f9b-7097-49d6-a3e3-38fd926561b4
-- title:
--   Monotonicity and existence of the critical radius (Lemma 13.6), for non-degenerate star-shaped classes
-- statement:
--   **Lemma 13.6** (p. 425). Let $x_1,\dots,x_n$ be fixed design points, $w_1,\dots,w_n$ i.i.d.
--   standard Gaussian noise, and let $\mathcal H$ be a star-shaped function class whose local
--   Gaussian complexity
--   $\mathcal G_n(\delta;\mathcal H)=\mathbb E_w\big[\sup_{h\in\mathcal H,\ \|h\|_n\le\delta}
--   \big|\tfrac1n\sum_{i=1}^n w_i h(x_i)\big|\big]$ (Eq. (13.16)) has a measurable defining supremum
--   for every $\delta>0$. Then the map $\delta\mapsto\mathcal G_n(\delta;\mathcal H)/\delta$ is
--   non-increasing on $(0,\infty)$. Consequently, if $\mathcal H$ is non-degenerate on the design
--   (some $h\in\mathcal H$ has $\|h\|_n\ne0$), then for any constant $c>0$ the inequality
--   $$
--   \frac{\mathcal G_n(\delta;\mathcal H)}{\delta}\le c\,\delta
--   $$
--   has a smallest positive solution.
--
--   This lemma is what makes sense of the phrase "let $\delta_n$ be any positive solution of
--   the critical inequality" in Theorems 13.5 and 13.13: it guarantees that valid radii exist
--   at all, and identifies the smallest one, $\delta_n^*$, as the natural choice.
--
--   **Formalization Note.** The retired version (`thm13_6_critical_radius_exists`) admitted
--   degenerate classes — $\mathcal H=\emptyset$, $\mathcal H=\{0\}$, $n=0$, or any class all of whose
--   members vanish at the design points — for which $\mathcal G_n\equiv0$, every $\delta>0$ solves
--   the inequality and no smallest positive solution exists (accepted disproof with
--   $\mathcal H=\emptyset$, $n=0$). The printed sentence is literally false for such $\mathcal H$ (it
--   tacitly assumes a nontrivial class), so the correction is the hypothesis
--   `hH0 : ∃ h ∈ H, empiricalNorm x h ≠ 0`, which excludes exactly the classes with
--   $\mathcal G_n\equiv 0$ (for Gaussian noise, $\mathcal G_n(\delta)>0$ for small $\delta$ as soon as
--   some $h\in\mathcal H$ has $\|h\|_n>0$, by star-shapedness) and in particular forces $n\ge1$. The
--   hypothesis `hmeas` (integrability of the defining supremum for every $\delta>0$) makes explicit
--   the field's standing measurability convention; the supremum is automatically bounded by
--   $\|w\|_n\delta$ (Cauchy–Schwarz), so it is a pure measurability condition, without which
--   Mathlib's Bochner integral would return the junk value $0$ at some radii and break the
--   monotonicity claim. $\mathcal G_n$ is `localGaussianComplexity` from the mission's `Core`;
--   the existence claim is stated as `IsLeast` of the solution set, matching "smallest positive
--   solution" literally.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 425 (PDF p. 445), Lemma 13.6 — with the tacit non-degeneracy of the class H (some h ∈ H with ‖h‖_n ≠ 0) made explicit; the printed sentence is false for degenerate classes such as H = {0}

import Mathlib
import Definitions.Def_HighDimStat_NonparametricLS_Core

namespace HighDimStat.NonparametricLS

open MeasureTheory

/-- **Lemma 13.6** (p. 425, PDF 445). For any star-shaped function class `H`, the map
`δ ↦ Gₙ(δ; H)/δ` is non-increasing on `(0, ∞)`. Consequently, for any constant `c > 0`, the
inequality `Gₙ(δ; H)/δ ≤ cδ` has a smallest positive solution — provided `H` is
non-degenerate on the design, i.e. some `h ∈ H` has `‖h‖ₙ ≠ 0`.

Corrections: the retired version admitted degenerate classes (`H = ∅`, `H = {0}`, `n = 0`, or
any `H` all of whose members vanish at the design points), for which `Gₙ ≡ 0`, every `δ > 0`
solves the inequality and no smallest positive solution exists; the printed sentence is false
for such `H` (it tacitly assumes a nontrivial class), so the non-degeneracy hypothesis `hH0`
is added as the correction. The integrability hypothesis `hmeas` makes explicit the field's
standing measurability convention for the supremum defining `Gₙ(δ; H)` (the supremum is
automatically bounded by `‖w‖ₙ δ`, so this is purely a measurability condition); without it
Mathlib's Bochner integral returns the junk value `0` for a non-measurable integrand. -/
theorem thm13_6_critical_radius_exists_v2 {X Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (x : Fin n → X) (w : Fin n → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hw : IsIIDStdGaussian P w)
    (H : Set (X → ℝ)) (hH : IsStarShaped H)
    (hH0 : ∃ h ∈ H, empiricalNorm x h ≠ 0)
    (hmeas : ∀ δ : ℝ, 0 < δ →
      Integrable (fun ω => ⨆ h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δ},
        |(∑ i, w i ω * h.1 (x i)) / n|) P) :
    (∀ δ t : ℝ, 0 < δ → δ ≤ t →
        localGaussianComplexity x w P H t / t ≤ localGaussianComplexity x w P H δ / δ) ∧
      ∀ c : ℝ, 0 < c →
        ∃ δ, IsLeast {δ : ℝ | 0 < δ ∧ localGaussianComplexity x w P H δ / δ ≤ c * δ} δ := by sorry

end HighDimStat.NonparametricLS
