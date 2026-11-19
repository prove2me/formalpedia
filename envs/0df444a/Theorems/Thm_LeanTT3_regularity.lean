-- Prove2me | Theorems.Thm_LeanTT3_regularity
-- name    : LeanTT3.regularity
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T14:44:46.771193+00:00
-- url     : https://prove2.me/theorems/2bb77842-d728-4395-9528-f07db2d98bb9
-- title:
--   Regularity (Lemma 3.1)
-- statement:
--   Every well-typed term has a well-typed type: if $\Gamma\vdash e:\alpha$ then $\alpha$ is itself a type, i.e. $\Gamma\vdash\alpha:\mathsf{U}_n$ for some universe level $n$. This is the regularity lemma (Lemma 3.1), recording the basic invariant of the typing judgment.
--
--   **Formalization Note.** Levels are concrete natural numbers in the proof-split language, so the universe is `E.sort n`.
-- source:
--   M. Carneiro, The Type Theory of Lean, Master's thesis, Carnegie Mellon University, 2019, https://github.com/digama0/lean-type-theory, Section 3.2, Lemma 3.1 (regularity, p. 17).

import Mathlib
import Definitions.Def_ltt3_judgments

namespace LeanTT3
set_option autoImplicit true in
theorem regularity : Ty Γ e α → ∃ n, Ty Γ α (E.sort n) := by sorry
end LeanTT3
