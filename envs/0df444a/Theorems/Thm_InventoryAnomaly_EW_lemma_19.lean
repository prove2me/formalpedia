-- Prove2me | Theorems.Thm_InventoryAnomaly_EW_lemma_19
-- name    : InventoryAnomaly.EW.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:27:01.75473+00:00
-- url     : https://prove2.me/theorems/cb9ad320-9b05-48b5-aeed-228d4a4f0be0
-- title:
--   Lemma 19, p. 46 — |x̂/(x̂+ŷ) − x/(x+y)| ≤ min(δ/(x+y), δ/(x̂+ŷ), 1) for δ-close x, y, x̂, ŷ ∈ [0, 1]
-- statement:
--   Let $x,y,\hat x,\hat y\in[0,1]$ with $x+y>0$, $|\hat x-x|\le\delta$ and $|\hat y-y|\le\delta$. Let $\hat s=\hat x/(\hat x+\hat y)$ if $\hat x+\hat y>0$ and $\hat s=0$ otherwise. Then
--   $$\Big|\hat s-\frac{x}{x+y}\Big|\le\min\Big(\frac{\delta}{x+y},\ \frac{\delta}{\hat x+\hat y},\ 1\Big),\qquad(34)$$
--   where the middle term is read as $+\infty$ when $\hat x+\hat y=0$.
--
--   It converts additive errors on the two likelihood terms into an error on the posterior probability $f=y/(x+y)$.
--
--   **Formalization Note.** The conclusion is stated as two parts: the bound by $\min(\delta/(x+y),1)$ always, and the bound by $\delta/(\hat x+\hat y)$ when $\hat x+\hat y>0$. This is the paper's convention: in Lean $\delta/0=0$, and the literal three-term minimum would then be false whenever $\hat x+\hat y=0$.
-- source:
--   Farias, Li & Peng, Fixing Inventory Inaccuracies at Scale, arXiv:2006.13126v3, p. 46, Lemma 19, eq. (34)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InventoryAnomaly.EW

theorem lemma_19 (x y xh yh δ : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (hxh : 0 ≤ xh ∧ xh ≤ 1) (hyh : 0 ≤ yh ∧ yh ≤ 1) (hxy : 0 < x + y)
    (h1 : |xh - x| ≤ δ) (h2 : |yh - y| ≤ δ) :
    let sh := if 0 < xh + yh then xh / (xh + yh) else 0
    |sh - x / (x + y)| ≤ min (δ / (x + y)) 1 ∧
      (0 < xh + yh → |sh - x / (x + y)| ≤ δ / (xh + yh)) := by sorry

end InventoryAnomaly.EW
