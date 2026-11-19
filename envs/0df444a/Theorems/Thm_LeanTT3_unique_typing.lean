-- Prove2me | Theorems.Thm_LeanTT3_unique_typing
-- name    : LeanTT3.unique_typing
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T14:46:52.803879+00:00
-- url     : https://prove2.me/theorems/c70eadfe-2a54-4938-a68b-7495d235184b
-- title:
--   Unique typing (Theorem 4.1)
-- statement:
--   If a term has two types in the same context, those types are definitionally equal: from $\Gamma\vdash e:\alpha$ and $\Gamma\vdash e:\beta$ it follows that $\Gamma\vdash\alpha\equiv\beta$. This is the unique-typing theorem (Theorem 4.1), the cornerstone of the metatheory; it is what makes the $\mathsf{lvl}$/$\mathsf{sort}$ functions well-defined and underpins the set-theoretic interpretation.
--
--   **Formalization Note.** `Deq` is the ideal definitional equality, defined mutually with `Ty`.
-- source:
--   M. Carneiro, The Type Theory of Lean, Master's thesis, Carnegie Mellon University, 2019, https://github.com/digama0/lean-type-theory, Section 4, Theorem 4.1 (unique typing, p. 18).

import Mathlib
import Definitions.Def_ltt3_judgments

namespace LeanTT3
set_option autoImplicit true in
theorem unique_typing : Ty Γ e α → Ty Γ e β → Deq Γ α β := by sorry
end LeanTT3
