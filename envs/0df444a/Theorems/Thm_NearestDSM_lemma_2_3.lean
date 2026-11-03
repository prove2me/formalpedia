-- Prove2me | Theorems.Thm_NearestDSM_lemma_2_3
-- name    : NearestDSM.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:18:23.232182+00:00
-- url     : https://prove2.me/theorems/73fa48f2-f456-4535-9517-b6930b7b63b2
-- title:
--   Lemma 2.3 — $V(M)$ is nonsingular iff $M$ is connected
-- statement:
--   Let $M\in\mathbb R^{n\times n}$ with $M\ge 0$ entrywise. Then
--   $$
--   V(M)=A\,\mathrm{Diag}(\mathrm{vec}(M))A^T\ \text{is nonsingular}\iff M\ \text{is connected},
--   $$
--   where $M$ is connected if its bipartite row–column graph (an edge for each nonzero entry) is connected.
--
--   This is the sufficient condition for nonsingularity of the generalized Jacobian used throughout the paper: it is why the Newton step is taken at a point where the maximal matrix is connected.
--
--   Differences from the source:
--   - encoding: size $n\ge1$ → `n + 1`, 0-based indices; nonsingular → $\det\ne 0$; reason: Lean convention, same instances
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, Lemma 2.3, p.9

import Mathlib
import Definitions.Def_NearestDSM_Vmat
import Definitions.Def_NearestDSM_IsConnectedMat

namespace NearestDSM

/-- Hu, Im, Li & Wolkowicz, arXiv:2107.09631v1, Lemma 2.3, p.9. Let `M ≥ 0`. The matrix `V(M) = A Diag(vec(M)) Aᵀ` is
nonsingular if, and only if, `M` is connected.

**Formalization Note.** The paper's size `n` is `n + 1`. "Nonsingular" is `det ≠ 0`; "connected"
is connectedness of the bipartite row–column graph of the nonzero entries of `M` (p.7). -/
theorem lemma_2_3 {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hM : ∀ a b, 0 ≤ M a b) :
    (Vmat M).det ≠ 0 ↔ IsConnectedMat M := by sorry

end NearestDSM
