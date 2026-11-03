-- Prove2me | Theorems.Thm_NearestDSM_theorem_3_4
-- name    : NearestDSM.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:20:32.841265+00:00
-- url     : https://prove2.me/theorems/ad1f20e4-6c41-47c4-bfa7-c41b30cc1467
-- title:
--   Theorem 3.4 — a connected $X$ has a singleton class
-- statement:
--   Let $\tilde y\in\mathbb R^{2n-1}$. If $\mathrm{Mat}(\hat x+A^T\tilde y)_+$ is connected, then the equivalence class $[\tilde y]$ is a singleton:
--   $$
--   [\tilde y]=\{\tilde y\}.
--   $$
--   In particular, if the optimal $X^*$ is connected, the optimal dual vector is unique (Corollary 3.5).
--
--   Differences from the source:
--   - encoding: size $n\ge1$ → `n + 1`; reason: Lean convention, same instances
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, Theorem 3.4, p.14

import Mathlib
import Definitions.Def_NearestDSM_IsConnectedMat
import Definitions.Def_NearestDSM_equivClass

namespace NearestDSM

/-- Hu, Im, Li & Wolkowicz, arXiv:2107.09631v1, Theorem 3.4, p.14. Let `ỹ ∈ ℝ^{2n−1}` be given. If `Mat(x̂ + Aᵀỹ)₊` is
connected, then the equivalence class `[ỹ]` is a singleton.

**Formalization Note.** The paper's size `n` is `n + 1`. -/
theorem theorem_3_4 {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (yt : Dual n)
    (hconn : IsConnectedMat (Xmat Xh yt)) : equivClass Xh yt = {yt} := by sorry

end NearestDSM
