-- Prove2me | Theorems.Thm_LefebvreVariations_dedekind_six_variables
-- name    : LefebvreVariations.dedekind_six_variables
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:09:35.365905+00:00
-- url     : https://prove2.me/theorems/2284d2dc-dfc1-4fec-adca-57ffebcd66d2
-- title:
--   Lefebvre's variations, No. 150 — on a theme by Dedekind: the number of monotone Boolean functions of six variables is 7828354
-- statement:
--   The number of monotone Boolean functions of $n$ variables, that is, of maps $f:\{0,1\}^n\to\{0,1\}$ with $x\le y\Rightarrow f(x)\le f(y)$ (coordinatewise order), the two constant functions included, is the Dedekind number $M(n)$. Then
--   $$M(6)=7828354 .$$
--   The first values are $M(0),\dots,M(5)=2,3,6,20,168,7581$.
--
--   **Formalization Note** The set is \texttt{\{f : (Fin n $\to$ Bool) $\to$ Bool // Monotone f\}} with the product order on \texttt{Fin n $\to$ Bool} and \texttt{false < true}; the statement is on its \texttt{Nat.card}.
--
--   **Why this is a variation.** There is no open platform problem for the Dedekind numbers as such; this is a stand-alone finite enumeration for the classical Dedekind problem (counting monotone Boolean functions) at n=6. No formal link to a platform parent is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   OEIS A000372 (Dedekind numbers); M(6) attributed to Ward (1946) (cited from memory). M(6) was also recomputed independently in python for this statement.

import Mathlib

namespace LefebvreVariations

/-- The Dedekind number `M(6) = 7828354`: the number of monotone Boolean functions of six
variables (constants included; `M(0),…,M(5) = 2, 3, 6, 20, 168, 7581`).
Source: OEIS A000372 (cited from memory for the original computation). -/
theorem dedekind_six_variables :
    Nat.card {f : (Fin 6 → Bool) → Bool // Monotone f} = 7828354 := by
  sorry

end LefebvreVariations
