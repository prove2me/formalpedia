-- Prove2me | Theorems.Thm_MultiStoreAssort_SQR_lemmaB4_quasiconvex
-- name    : MultiStoreAssort.SQR.lemmaB4_quasiconvex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:16.212191+00:00
-- url     : https://prove2.me/theorems/bf4017eb-450f-41ae-a4bf-5e8ba094f2e2
-- title:
--   Lemma B.4, PDF p. 39 — f(x) = Σᵢ (aᵢ + bᵢx)/(dᵢ + x) is quasi-convex on x ≥ 0 when aᵢ/bᵢ decreases and dᵢ increases
-- statement:
--   Let $a_1,\dots,a_m>0$ and $b_1,\dots,b_m>0$ with
--   $$
--   \frac{a_1}{b_1}\ge\frac{a_2}{b_2}\ge\dots\ge\frac{a_m}{b_m},
--   $$
--   and let $0<d_1\le d_2\le\dots\le d_m$. Then the function
--   $$
--   f(x)=\sum_{i=1}^m\frac{a_i+b_ix}{d_i+x}
--   $$
--   is quasi-convex on $[0,\infty)$: for $0\le x,y$ and $\theta\in[0,1]$, $f(\theta x+(1-\theta)y)\le\max\{f(x),f(y)\}$.
--
--   In the proof of Proposition B.2 the revenue difference created by adding a product to store $m$ takes this form, and quasi-convexity shows that adding it or removing the tail of store $m$ never hurts.
--
--   **Formalization Note.** Quasi-convexity is Mathlib's `QuasiconvexOn ℝ (Set.Ici 0) f` (convex sublevel sets), which is equivalent to the inequality above. The statement is as printed; the paper later applies it with some $a_i=0$ and a reordered index, which is not covered here.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 39, Lemma B.4 (proof in the Additional Supplement, PDF pp. 53–54)

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

namespace MultiStoreAssort.SQR

theorem lemmaB4_quasiconvex {m : ℕ} (a b d : Fin m → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hab : Antitone (fun i => a i / b i)) (hd0 : ∀ i, 0 < d i) (hd : Monotone d) :
    QuasiconvexOn ℝ (Set.Ici (0 : ℝ)) (fun x => ∑ i, (a i + b i * x) / (d i + x)) := by sorry

end MultiStoreAssort.SQR
