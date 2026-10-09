-- Prove2me | Theorems.Thm_MultiItemRev_KBundling_lemma_21
-- name    : MultiItemRev.KBundling.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:11:50.009816+00:00
-- url     : https://prove2.me/theorems/8f04f772-9be5-4558-b938-9b7ff96bf41c
-- title:
--   Lemma 21, p. 37 — the tail of αV₁ + βV₂ for i.i.d.-ER V₁, V₂
-- statement:
--   **Lemma 21.** Let $V_1,V_2$ be i.i.d.-ER and let $\alpha,\beta>0$. Then for every real $z$:
--
--   1. if $z\ge\alpha+\beta$,
--   $$\mathbb P[\alpha V_1+\beta V_2\ge z]=\frac{\alpha\beta}{z^2}\ln\Big(1+\frac{z^2-(\alpha+\beta)z}{\alpha\beta}\Big)+\frac{\alpha+\beta}{z};$$
--   2. if $z\le\alpha+\beta$, then $\mathbb P[\alpha V_1+\beta V_2\ge z]=1$.
--
--   The closed form for the tail of a weighted sum of two ER goods is what makes the bundling revenue of two ER goods computable (Proposition 24).
--
--   **Formalization Note** $V_1,V_2$ are the coordinates of the product of two copies of the ER law on `Fin 2 → ℝ≥0`; the law of $\alpha V_1+\beta V_2$ is its image in $\mathbb R$, so $z$ ranges over all reals. The probability is in `ℝ≥0∞`, the formula enters through `ENNReal.ofReal`.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 37, Lemma 21

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model
import Definitions.Def_MultiItemRev_KSeparate_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KBundling

theorem lemma_21 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (z : ℝ) :
    (α + β ≤ z →
      (Measure.pi (fun _ : Fin 2 => MultiItemRev.KSeparate.erLaw)).map
          (fun x => α * (x 0 : ℝ) + β * (x 1 : ℝ)) {t | z ≤ t} =
        ENNReal.ofReal (α * β / z ^ 2 *
            Real.log (1 + (z ^ 2 - (α + β) * z) / (α * β)) + (α + β) / z)) ∧
    (z ≤ α + β →
      (Measure.pi (fun _ : Fin 2 => MultiItemRev.KSeparate.erLaw)).map
          (fun x => α * (x 0 : ℝ) + β * (x 1 : ℝ)) {t | z ≤ t} = 1) := by sorry

end MultiItemRev.KBundling
