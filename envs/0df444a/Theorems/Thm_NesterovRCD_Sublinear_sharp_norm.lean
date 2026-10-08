-- Prove2me | Theorems.Thm_NesterovRCD_Sublinear_sharp_norm
-- name    : NesterovRCD.Sublinear.sharp_norm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:24.908505+00:00
-- url     : https://prove2.me/theorems/ea079eeb-b90f-4132-908d-3516ea9c5591
-- title:
--   §1, after (1.8) — $\|s^\#\|=\|s\|_*$ (and $\langle s,s^\#\rangle=\|s\|_*^2$)
-- statement:
--   Let $F$ be a finite-dimensional real normed space, $s$ a linear functional on $F$ with dual norm $\|s\|_*=\max_{\|h\|=1}\langle s,h\rangle$, and let $s^\#$ be any vector of
--   $$\operatorname{Arg\,max}_x\Big[\langle s,x\rangle-\tfrac12\|x\|^2\Big].$$
--   Then
--   $$\|s^\#\|=\|s\|_*\qquad\text{and}\qquad\langle s,s^\#\rangle=\|s\|_*^2 .$$
--
--   The first identity is the claim "Clearly, $\|s^\#\|=\|s\|_*$" of the paper; the second is the companion identity that makes the optimal coordinate step $T_i$ decrease the objective by exactly the amount used in (2.4).
--
--   **Formalization Note** The dual norm is the operator norm of `F →L[ℝ] ℝ`. Finite dimensionality makes the max in (1.7) attained, as for the paper's $\mathbb R^{n_i}$. The second conjunct is not printed in the paper and is added as part of this milestone.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 3, §1 (Notation), after (1.8)

import Mathlib
import Definitions.Def_NesterovRCD_Sublinear_Basic

namespace NesterovRCD.Sublinear

theorem sharp_norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (s : F →L[ℝ] ℝ) (v : F) (hv : IsSharp s v) :
    ‖v‖ = ‖s‖ ∧ s v = ‖s‖ ^ 2 := by sorry

end NesterovRCD.Sublinear
