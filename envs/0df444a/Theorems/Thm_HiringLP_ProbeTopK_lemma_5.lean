-- Prove2me | Theorems.Thm_HiringLP_ProbeTopK_lemma_5
-- name    : HiringLP.ProbeTopK.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:23.567223+00:00
-- url     : https://prove2.me/theorems/7db72ec8-77b9-4e6e-ad62-e300a7bd459d
-- title:
--   Lemma 5 — for weighted Bernoulli instances, LPptk has an optimal solution with x_i = y_i q_i
-- statement:
--   Let $I$ be a weighted Bernoulli instance: applicant $i$'s value is $r_i \ge 0$ with probability $q_i \in [0,1]$ and $0$ otherwise, with $1 \le k \le T \le n$. Consider $\mathrm{LP}_{ptk}$ rewritten for these instances,
--
--   $$
--   \max \sum_i r_i x_i \quad\text{s.t.}\quad x_i \le y_i q_i,\ \ \sum_i y_i \le T,\ \ \sum_i x_i \le k,\ \ x_i \ge 0,\ \ 0 \le y_i \le 1 .
--   $$
--
--   Then this LP has an optimal solution $(x, y)$ with
--
--   $$
--   x_i = y_i q_i \quad \text{for all } i \in [n].
--   $$
--
--   With such a solution ALGptk hires every interviewed applicant whose value is $r_i$, which makes it a valid policy for the Sequential Offering problem with the same guarantee (Corollary 2).
--
--   **Formalization Note.** The statement asserts existence of an optimal solution with the property, as on the page.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 21, Lemma 5

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_WeightedBernoulli

namespace HiringLP.ProbeTopK

theorem lemma_5 {n : ℕ} (I : WBInstance n) (hI : I.Valid) :
    ∃ x y : Fin n → ℝ, WBIsOpt I x y ∧ ∀ i, x i = y i * I.q i := by sorry

end HiringLP.ProbeTopK
