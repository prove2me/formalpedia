-- Prove2me | Theorems.Thm_MartOT_Var_badTuples_measurableSet
-- name    : MartOT.Var.badTuples_measurableSet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:16.040709+00:00
-- url     : https://prove2.me/theorems/0b672aa4-bd2a-41b1-a828-b9700a3715aa
-- title:
--   Proof of Lemma 1.11, p. 17 — for a Borel cost c, the set M of bad n-tuples is Borel
-- statement:
--   Let $c:\mathbb R\times\mathbb R\to\mathbb R$ be Borel measurable and $n\in\mathbb N$. Then the set
--   $$M=\Big\{(x_i,y_i)_{i=1}^n:\ \exists\text{ finite }\alpha \text{ concentrated on }\{(x_i,y_i)\},\ \exists\text{ competitor }\alpha'\text{ of }\alpha,\ \int c\,d\alpha'<\int c\,d\alpha\Big\}$$
--   of $n$-tuples carrying a non-optimal finitely supported measure is a Borel subset of $(\mathbb R\times\mathbb R)^n$.
--
--   The paper asserts this when it introduces $M$ ("define a Borel set $M$"); it is what allows Theorem 3.1 to be applied to $M$.
--
--   **Formalization Note** $(\mathbb R\times\mathbb R)^n$ is `Fin n → ℝ × ℝ` with the product $\sigma$-algebra, which is its Borel $\sigma$-algebra. $M$ is the definition `BadTuples` (finite $\alpha$, support condition written as $\alpha(F^c)=0$).
-- source:
--   arXiv:1208.1509v2, §3, proof of Lemma 1.11, p. 17 ("For a fixed n ∈ N, define a Borel set M by")

import Mathlib
import Definitions.Def_MartOT_Var_BadTuples

namespace MartOT.Var

open MeasureTheory

theorem badTuples_measurableSet (c : ℝ → ℝ → ℝ) (hc : Measurable (Function.uncurry c))
    (n : ℕ) : MeasurableSet (BadTuples c n) := by sorry

end MartOT.Var
