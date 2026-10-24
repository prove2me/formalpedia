-- Prove2me | Theorems.Thm_IwataFF_SFM_augmentations_per_phase
-- name    : IwataFF.SFM.augmentations_per_phase
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:26.669968+00:00
-- url     : https://prove2.me/theorems/b82a4313-632f-4ecc-9db5-ce5d4a79cd90
-- title:
--   §3.3, p. 11 — at most $n^2 + n$ δ-augmentations in every scaling phase after the first
-- statement:
--   Let $V$ be a finite nonempty set with $|V| = n$ and $f$ submodular on $V$ with $f(\emptyset) = 0$. Let $s_0, s_1, \dots, s_m$ ($m \ge 1$) be states of the scaling algorithm such that $s_0$ satisfies the invariants and is the end of a phase that has begun (a $2\delta$-scaling phase), $s_1$ is obtained from $s_0$ by starting the next phase ($\delta \leftarrow \delta/2$ and clipping $\varphi$), and each $s_{j+1}$, $1 \le j < m$, is obtained from $s_j$ by a push or by an augmentation with its reduction. Then the number of augmentations among these steps is at most
--   $$n^2 + n.$$
--
--   **Formalization Note** The run may stop anywhere inside the phase; the bound counts the augmentations performed so far. $f$ is real-valued (the argument never uses integrality).
-- source:
--   Iwata, Fleischer & Fujishige, A Combinatorial, Strongly Polynomial-Time Algorithm for Minimizing Submodular Functions, arXiv:math/0004089v1, p. 11, §3.3 (number of δ-augmentations per phase)

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic
import Definitions.Def_IwataFF_SFM_Phase

namespace IwataFF.SFM

/-- §3.3, p. 11 (arXiv:math/0004089v1): in every δ-scaling phase after the first, the number of
δ-augmentations is at most `n² + n`. -/
theorem augmentations_per_phase {α : Type} [DecidableEq α] (V : Finset α) (hV : V.Nonempty)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (s : ℕ → PhaseState α) (m : ℕ) (hinv : PhaseInv V (s 0)) (hrun : IsPhaseRun f V s m) :
    augCount f V s m ≤ V.card ^ 2 + V.card := by sorry

end IwataFF.SFM
