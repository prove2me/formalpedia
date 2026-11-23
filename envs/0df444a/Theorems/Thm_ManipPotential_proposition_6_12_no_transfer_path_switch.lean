-- Prove2me | Theorems.Thm_ManipPotential_proposition_6_12_no_transfer_path_switch
-- name    : ManipPotential.proposition_6_12_no_transfer_path_switch
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:38:38.238235+00:00
-- url     : https://prove2.me/theorems/c5192e72-2ba8-4313-b168-6e559b16dc3e
-- title:
--   No transfer path can switch the winner from $c_i$ to $c_j$
-- statement:
--   Let $g$ satisfy bounded manipulation potential with $\lambda=K+1$, and let $c_i\ne c_j$. Suppose
--   $Q_0,Q_1,\ldots,Q_L$ is a finite sequence of rational profiles such that every consecutive pair is a
--   positive transfer step for $(c_i,c_j)$ as in Eq. (17), with nonnegative replacement background. If
--   $g(Q_k)\in\{c_i,c_j\}$ at every visited profile, $g(Q_0)=c_i$, and $g(Q_L)=c_j$, then no such sequence
--   exists:
--   $$
--   \bigl(g(Q_0)=c_i\ \wedge\ g(Q_L)=c_j\bigr)\quad\Longrightarrow\quad\bot.
--   $$
--   This isolates the final first-switch argument in Proposition 6.12, Step 1. The two orientations of a
--   transfer vector give, respectively, $g(Q')\succeq_r c_i$ when $c_i\succ_r c_j$, and
--   $c_i\succeq_r g(Q')$ when $c_j\succ_r c_i$; either comparison contradicts $g(Q')=c_j$.
--
--   **Formalization Note** The path is represented by a function `Q : ℕ → Ranking m → ℚ` with steps
--   through index `L`. The conclusion `False` makes the result directly applicable to a path extracted
--   from the analytic reference-curve construction.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Proposition 6.12, Step 1, final first-switch argument, p.37; transfer vectors (17), p.35.

import Mathlib
import Definitions.Def_ManipPotential_TransferStep
import Definitions.Def_ManipPotential_BoundedMP

open ManipPotential

/-- Along a finite path of positive transfer steps for the pair `(i,j)`, bounded manipulation
potential prevents the winner from changing from `i` to `j` when every visited winner is in
that pair. -/
theorem ManipPotential.proposition_6_12_no_transfer_path_switch {m : ℕ} (K : ℕ)
    (g : (Ranking m → ℚ) → Fin m) (hg : BoundedMP K g) (i j : Fin m)
    (hij : i ≠ j) (L : ℕ) (Q : ℕ → Ranking m → ℚ)
    (hstart : g (Q 0) = i) (hend : g (Q L) = j)
    (hwinners : ∀ k ≤ L, g (Q k) = i ∨ g (Q k) = j)
    (hsteps : ∀ k < L, TransferStep K i j (Q k) (Q (k + 1))) : False := by sorry
