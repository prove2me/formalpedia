-- Prove2me | Theorems.Thm_HoffmanBound_ErrorBound_lemma4
-- name    : HoffmanBound.ErrorBound.lemma4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:37:06.397512+00:00
-- url     : https://prove2.me/theorems/a9744adc-641d-4c82-adad-792779ba0198
-- title:
--   Lemma 4 — the cone K′ spanned by the rows of M, origin deleted, equals E
-- statement:
--   Let $S$ be a set of rows of $A$, let $M$ be the matrix obtained from $A$ by substituting $0$ for the rows not in $S$, with rows $M_1,\dots,M_m$, and let $E$ be the set of Lemma 3: the points $x$ exterior to $\Omega_0=\{z : Mz\le 0\}$ whose nearest point in $\Omega_0$ is the origin. Let
--   $$
--   K'=\Bigl\{\textstyle\sum_{i=1}^m\lambda_iM_i : \lambda_i\ge 0\Bigr\}\setminus\{0\}
--   $$
--   be the cone spanned by the row vectors of $M$, with the origin deleted. Then
--   $$
--   K'=E.
--   $$
--
--   This gives a description of $E$ by the rows of $M$, which Sections 4 and 5 use to compute the constant of the main theorem for the max and sum norms.
-- source:
--   Hoffman, On Approximate Solutions of Systems of Linear Inequalities, J. Res. Nat. Bur. Standards 49 (1952), p. 264 (PDF p. 2), Lemma 4

import Mathlib
import Definitions.Def_HoffmanBound_ErrorBound_Model

namespace HoffmanBound.ErrorBound

/-- Hoffman 1952, p. 264, Lemma 4. With `M = rowsOn A S` and `E` as in Lemma 3, the cone spanned by
the row vectors of `M` with the origin deleted equals `E`. -/
theorem lemma4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m)) :
    conePrime A S = setE A S := by sorry

end HoffmanBound.ErrorBound
