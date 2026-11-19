-- Prove2me | Theorems.Thm_LeanTT3_consistency
-- name    : LeanTT3.consistency
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T14:47:14.945696+00:00
-- url     : https://prove2.me/theorems/4aef7a55-8834-438a-bf6e-bedf6a2de316
-- title:
--   Consistency of the kernel (no closed proof of $\bot$)
-- statement:
--   There is no closed term of the empty type: no expression $e$ satisfies the ideal typing judgment $\vdash e:\bot$ in the empty context. Since the kernel's algorithmic equality implies the ideal definitional equality, no proof of $\bot$ is verified by the Lean kernel either. This is the consistency corollary of Section 6, derived there from the set-theoretic soundness theorem; combined with the $\mathsf{W}$-type reduction of Part II it applies to the full kernel.
--
--   **Formalization Note.** $\bot$ is the primitive empty type `E.empty` of the proof-split menagerie, and `Ty` is the inductively defined ideal typing judgment.
-- source:
--   M. Carneiro, The Type Theory of Lean, Master's thesis, Carnegie Mellon University, 2019, https://github.com/digama0/lean-type-theory, Section 6, consistency corollary (p. 31).

import Mathlib
import Definitions.Def_ltt3_judgments

namespace LeanTT3
set_option autoImplicit true in
theorem consistency : ¬ ∃ e, Ty [] e E.empty := by sorry
end LeanTT3
