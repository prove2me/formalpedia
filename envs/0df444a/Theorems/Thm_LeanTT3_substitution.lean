-- Prove2me | Theorems.Thm_LeanTT3_substitution
-- name    : LeanTT3.substitution
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T14:46:13.393776+00:00
-- url     : https://prove2.me/theorems/b237b012-fd8f-459e-846c-a747f5f5a6b4
-- title:
--   Substitution (Lemma 3.3)
-- statement:
--   Typing is preserved under substitution: if $\Gamma,x:\alpha\vdash e:\beta$ and $\Gamma\vdash a:\alpha$, then $\Gamma\vdash e[a/x]:\beta[a/x]$. This is the substitution lemma (Lemma 3.3), proved simultaneously with the corresponding statement for definitional equality.
--
--   **Formalization Note.** `E.inst e a` substitutes `a` for the outermost de Bruijn index (index 0) in `e`.
-- source:
--   M. Carneiro, The Type Theory of Lean, Master's thesis, Carnegie Mellon University, 2019, https://github.com/digama0/lean-type-theory, Section 3.2, Lemma 3.3 (properties of substitution, p. 17).

import Mathlib
import Definitions.Def_ltt3_judgments

namespace LeanTT3
set_option autoImplicit true in
theorem substitution : Ty (α::Γ) e β → Ty Γ a α → Ty Γ (E.inst e a) (E.inst β a) := by sorry
end LeanTT3
