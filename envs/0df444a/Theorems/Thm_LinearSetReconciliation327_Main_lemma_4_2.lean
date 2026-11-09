-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_lemma_4_2
-- name    : LinearSetReconciliation327.Main.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:35.617762+00:00
-- url     : https://prove2.me/theorems/4062b2a9-0e85-4119-be3b-1a1a2f3acccc
-- title:
--   Lemma 4.2 — McDiarmid extension for a uniform injection
-- statement:
--   Let $\pi:[D]\hookrightarrow[N]$ be a uniform injection independent of mutually independent $R_1,\dots,R_b$ with arbitrary laws on arbitrary measurable spaces, and $F(\pi,R)$ real-valued, measurable in $R$. If $|F(\tau\circ\pi,R)-F(\pi,R)|\le L_p$ for every transposition $\tau$ of $[N]$, $|F(\pi,R')-F(\pi,R)|\le L_r$ whenever $R,R'$ differ in one coordinate, and $DL_p^2+bL_r^2>0$, then for all $t>0$, $\Pr[F-\mathbb EF\ge t]\le\exp(-2t^2/(DL_p^2+bL_r^2))$.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
--   - encoding: mutually independent random variables R_i and π → product law of the laws μ_i, with π uniform and averaged explicitly; reason: a mutually independent family has exactly this joint law; F has an integral because bounded differences bound F(π,·)
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Lemma 4.2, PDF p.16–17 (printed p.15–16)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Lemma 4.2 (An extension of McDiarmid's inequality), PDF pp.16–17 (printed pp.15–16). The law of
`(R_1, …, R_b)` is the product of the laws `μ i`, which is mutual independence, and `π` is uniform
and independent of it, so `Pr` and `E` average over `π` an integral over `R`. -/
theorem lemma_4_2 (D N b : ℕ) (hDN : D ≤ N)
    (E : Fin b → Type) [∀ i, MeasurableSpace (E i)]
    (μ : ∀ i, MeasureTheory.Measure (E i)) [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (F : (Fin D ↪ Fin N) → (∀ i, E i) → ℝ) (hF : ∀ π, Measurable (F π))
    (Lp Lr : ℝ) (hLp : 0 ≤ Lp) (hLr : 0 ≤ Lr)
    (hp : ∀ (π : Fin D ↪ Fin N) (R : ∀ i, E i) (a c : Fin N),
      |F (π.trans (Equiv.swap a c).toEmbedding) R - F π R| ≤ Lp)
    (hr : ∀ (π : Fin D ↪ Fin N) (R R' : ∀ i, E i) (i : Fin b), (∀ i' , i' ≠ i → R i' = R' i') →
      |F π R' - F π R| ≤ Lr)
    (hpos : 0 < (D : ℝ) * Lp ^ 2 + (b : ℝ) * Lr ^ 2) (t : ℝ) (ht : 0 < t) :
    let P := MeasureTheory.Measure.pi μ
    let card : ℝ := Fintype.card (Fin D ↪ Fin N)
    let EF : ℝ := (∑ π : Fin D ↪ Fin N, ∫ R, F π R ∂P) / card
    (∑ π : Fin D ↪ Fin N, (P {R | t ≤ F π R - EF}).toReal) / card ≤
      Real.exp (-(2 * t ^ 2 / ((D : ℝ) * Lp ^ 2 + (b : ℝ) * Lr ^ 2))) := by sorry

end LinearSetReconciliation327.Main
