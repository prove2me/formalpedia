-- Prove2me | Theorems.Thm_Komlos_spencer_six_deviations_small
-- name    : Komlos.spencer_six_deviations_small
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T01:45:07.309119+00:00
-- url     : https://prove2.me/theorems/ef40bebd-a977-4634-aa45-28365e01148a
-- title:
--   Spencer's six-deviations bound in the trivial range $n \le 36$
-- statement:
--   **Spencer's theorem in the trivial range $n \le 36$.**
--
--   Spencer's "six standard deviations suffice" theorem states that for any $n \times n$ matrix $A$ with entries in $\{0,1\}$ there exist signs $\varepsilon_j \in \{\pm 1\}$ with
--   $$\Big|\sum_{j=1}^{n} A_{ij}\,\varepsilon_j\Big| \le 6\sqrt{n} \qquad \text{for every } i.$$
--
--   This statement restricts the claim to $n \le 36$, where it holds for a soft reason and requires none of Spencer's partial-colouring machinery. Every row sum of a $\{0,1\}$-matrix under the all-ones colouring lies in $[0, n]$, so the discrepancy of that colouring is at most $n$; and $n \le 6\sqrt{n}$ precisely when $n \le 36$. The threshold is sharp for this argument: at $n = 36$ the two bounds coincide ($36 = 6\sqrt{36}$), and for $n > 36$ the trivial colouring no longer suffices, which is exactly where the real content of Spencer's theorem begins.
--
--   It is recorded separately because any proof of the general theorem by induction, by dimension reduction, or by the entropy method needs a base range in which the conclusion is available for free, and because it fixes the arithmetic of the constant $6$ against the statement.
-- source:
--   Base range of J. Spencer, Six standard deviations suffice, Trans. Amer. Math. Soc. 289 (1985), 679-706, Theorem 1 (the 6*sqrt(n) bound). This is the range n <= 36 in which the bound follows from the trivial estimate |sum_j A_ij eps_j| <= n and n <= 6*sqrt(n); it uses none of the partial-colouring argument of that paper. Companion to the platform statement Komlos.spencer_six_deviations.

import Mathlib
import Definitions.Def_Komlos_model

namespace Komlos

theorem spencer_six_deviations_small (n : ℕ) (hn : n ≤ 36) (A : Fin n → Fin n → ℝ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    ∃ ε : Fin n → ℝ, IsSignVector ε ∧
      ∀ i, |∑ j, A i j * ε j| ≤ 6 * Real.sqrt n := by sorry

end Komlos
