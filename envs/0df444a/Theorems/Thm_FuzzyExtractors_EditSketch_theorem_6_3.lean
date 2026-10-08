-- Prove2me | Theorems.Thm_FuzzyExtractors_EditSketch_theorem_6_3
-- name    : FuzzyExtractors.EditSketch.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:55.12036+00:00
-- url     : https://prove2.me/theorems/4911a92e-7267-4130-9546-342e76517eff
-- title:
--   Theorem 6.3 — PinSketch is an average-case $(\mathrm{SDif}(\mathcal U), m, m - t\log(n+1), t)$ secure sketch
-- statement:
--   Let $K$ be a finite field of characteristic $2$, so that $\mathcal U = K^*$ has $n = 2^\mu - 1$ elements, and let $\mathrm{SDif}(\mathcal U)$ be the set of all subsets of $\mathcal U$ with the distance $|w \triangle w'|$. For every $t \in \mathbb N$ and every real $m$, PinSketch (Construction 6) with parameter $t$ is an average-case
--   $$\big(\mathrm{SDif}(\mathcal U),\ m,\ m - t\log(n + 1),\ t\big)$$
--   secure sketch. Its output $(s_1, s_3, \dots, s_{2t-1}) \in K^t$ has storage $t \log(n+1)$ bits.
--
--   PinSketch is the set-difference sketch that the edit-distance construction of §7 runs on the shingle set; its entropy loss $t\log(n+1)$ is the second term of the loss in Theorem 7.5.
--
--   **Formalization Note.** The paper's $GF(2^m)$ is any finite field `K` of characteristic $2$; the field degree is renamed $\mu$, so $\log(n + 1) = \mu$. The storage claim is the type `Fin t → K` of the sketch. The running-time sentence ("SS and Rec both run in time polynomial in $t$ and $\log n$") is dropped. Subsets have any size (no fixed-size restriction). The recovery procedure is `pinRec` of the definitions module, which outputs $w'$ when no light $v$ with the given odd syndromes exists.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, Theorem 6.3, p. 23

import Mathlib
import Definitions.Def_FuzzyExtractors_EditSketch_Basic

namespace FuzzyExtractors.EditSketch

theorem theorem_6_3 {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]
    (t : ℕ) (m : ℝ) :
    FuzzyExtractors.Hamming.IsAvgSecureSketch (symmDiffDis (U := Kˣ)) m
      (m - (t : ℝ) * Real.logb 2 ((Fintype.card Kˣ : ℝ) + 1)) t
      (pinSS (K := K) t) (pinRec t) := by sorry

end FuzzyExtractors.EditSketch
