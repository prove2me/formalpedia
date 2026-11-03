-- Prove2me | Theorems.Thm_NearestDSM_lemma_3_3
-- name    : NearestDSM.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:33.438441+00:00
-- url     : https://prove2.me/theorems/38c267f6-a04d-4219-8fda-4f31ccdd9792
-- title:
--   Lemma 3.3 — the solution set is an equivalence class
-- statement:
--   The solution set $\{y\mid F(y)=0\}$ of the system (2.5) is an equivalence class: there is $\tilde y\in\mathbb R^{2n-1}$ with
--   $$
--   \{y\in\mathbb R^{2n-1}\mid F(y)=0\}=[\tilde y].
--   $$
--   This is what justifies writing the solution set as $[y^*]$; it follows from the uniqueness of the optimal $X^*$.
--
--   Differences from the source:
--   - encoding: size $n\ge1$ → `n + 1`; reason: Lean convention, same instances
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, Lemma 3.3, p.14

import Mathlib
import Definitions.Def_NearestDSM_equivClass
import Definitions.Def_NearestDSM_solSet

namespace NearestDSM

/-- Hu, Im, Li & Wolkowicz, arXiv:2107.09631v1, Lemma 3.3, p.14. The solution set `{y | F(y) = 0}` of the system (2.5)
is an equivalence class.

**Formalization Note.** The paper's size `n` is `n + 1`. "Is an equivalence class" is
`∃ ỹ, {y | F(y) = 0} = [ỹ]`. -/
theorem lemma_3_3 {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ∃ yt : Dual n, solSet Xh = equivClass Xh yt := by sorry

end NearestDSM
