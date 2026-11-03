-- Prove2me | Theorems.Thm_NearestDSM_lemma_4_1
-- name    : NearestDSM.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:19:58.001051+00:00
-- url     : https://prove2.me/theorems/c734fc21-0a51-4f0b-9f0a-bd90d864566c
-- title:
--   Lemma 4.1 — the positive pattern of $x^*$ persists near $y^*$
-- statement:
--   Suppose $F(y^*)=0$, and write $x^*=(\hat x+A^Ty^*)_+$, $z^*=(\hat x+A^Ty^*)_-$. There exists $\epsilon>0$ such that for every $y$ with $\|y-y^*\|<\epsilon$,
--   $$
--   x^*_i>0\ \Longrightarrow\ x_i>0,\qquad x=(\hat x+A^Ty)_+ .
--   $$
--   Moreover, if $(x^*,z^*)$ satisfies strict complementarity, $x^*+z^*>0$, then $\epsilon$ can be taken such that also $x_i>0\Rightarrow x^*_i>0$.
--
--   The lemma lets the proof of Lemma 3.16 compare the block structure of $X$ near the solution with that of $X^*$.
--
--   **Formalization Note** $v_-=\max\{-v,0\}$ entrywise (the absolute value of the projection onto the nonpositive orthant, p.4); the norm is Euclidean.
--
--   Differences from the source:
--   - encoding: size $n\ge1$ → `n + 1`; reason: Lean convention, same instances
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, Lemma 4.1, p.25 (strict complementarity p.25, v₋ p.4)

import Mathlib
import Definitions.Def_NearestDSM_Fres
import Definitions.Def_NearestDSM_Xmat

namespace NearestDSM

/-- Hu, Im, Li & Wolkowicz, arXiv:2107.09631v1, Lemma 4.1, p.25. Suppose `F(y∗) = 0`. There exists `ε > 0` such that for
every `y` with `‖y − y∗‖ < ε`, `x∗_i > 0 ⟹ x_i > 0` (4.1), where `x = (x̂ + Aᵀy)₊` and
`x∗ = (x̂ + Aᵀy∗)₊`. Moreover, if `(x∗, z∗)` satisfies strict complementarity, `x∗ + z∗ > 0` with
`z∗ = (x̂ + Aᵀy∗)₋` (p.5, p.25), then `ε` can also be taken such that `x∗_i > 0 ⟸ x_i > 0`.

**Formalization Note.** `v₋ = max(−v, 0)` is the absolute value of the projection onto the
nonpositive orthant (p.4). The norm is Euclidean. The paper's size `n` is `n + 1`. -/
theorem lemma_4_1 {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (ys : Dual n) (hs : Fres Xh ys = 0) :
    (∃ ε > 0, ∀ y : Dual n, ‖y - ys‖ < ε → ∀ a b, 0 < Xmat Xh ys a b → 0 < Xmat Xh y a b) ∧
      ((∀ a b, 0 < Xmat Xh ys a b + max (-Ymat Xh ys a b) 0) →
        ∃ ε > 0, ∀ y : Dual n, ‖y - ys‖ < ε →
          ∀ a b, (0 < Xmat Xh ys a b ↔ 0 < Xmat Xh y a b)) := by sorry

end NearestDSM
