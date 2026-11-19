-- Prove2me | Theorems.Thm_LeanTT3_weakening
-- name    : LeanTT3.weakening
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T14:45:26.562759+00:00
-- url     : https://prove2.me/theorems/52fcc2ee-ba47-40f7-a63e-d718da5b55df
-- title:
--   Weakening (Lemma 3.2)
-- statement:
--   Typing is preserved when the context is extended by one binder: if $\Gamma\vdash e:\alpha$, then in the extended context $\Gamma,x:\beta$ the term and type (with de Bruijn indices shifted past the new binder) still satisfy the typing judgment. This is the one-binder step of the weakening lemma (Lemma 3.2).
--
--   **Formalization Note.** `E.lift 0 1` shifts all de Bruijn indices up by one to account for the newly inserted head binder `β`.
-- source:
--   M. Carneiro, The Type Theory of Lean, Master's thesis, Carnegie Mellon University, 2019, https://github.com/digama0/lean-type-theory, Section 3.2, Lemma 3.2 (weakening, p. 17).

import Mathlib
import Definitions.Def_ltt3_judgments

namespace LeanTT3
set_option autoImplicit true in
theorem weakening : Ty Γ e α → Ty (β::Γ) (E.lift 0 1 e) (E.lift 0 1 α) := by sorry
end LeanTT3
