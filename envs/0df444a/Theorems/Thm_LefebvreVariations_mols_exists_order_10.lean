-- Prove2me | Theorems.Thm_LefebvreVariations_mols_exists_order_10
-- name    : LefebvreVariations.mols_exists_order_10
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:10:14.477371+00:00
-- url     : https://prove2.me/theorems/8ec17a62-b491-5f47-afbe-9aa057d548e0
-- title:
--   Lefebvre's variations, No. 154 — on a theme by Bose, Shrikhande and Parker: there is a pair of orthogonal Latin squares of order 10
-- statement:
--   There exist maps $f:\{0,\dots,9\}^2\to\{0,\dots,9\}^2$ with first and second coordinates $f_1,f_2$ such that $f$ is injective, and for every row $r$ the maps $c\mapsto f_1(r,c)$ and $c\mapsto f_2(r,c)$ are injective, and for every column $c$ the maps $r\mapsto f_1(r,c)$ and $r\mapsto f_2(r,c)$ are injective.
--
--   That is, there is a pair of orthogonal Latin squares of order 10 (a Graeco-Latin square of order 10). The pair exists for every order $n\ne2,6$ (Bose–Shrikhande–Parker 1960); the platform problem `MOLS.existence` asks for this for all $n$. Order 10 is the smallest order that is neither a prime power nor covered by MacNeish's product construction, and it is the case of Euler's 'thirty-six officers' neighbour: order 6 has no such pair, order 10 does (Parker, 1959).
--
--   **Formalization Note** The conditions are the fields of the platform structure `MOLS n` with `n = 10`, written out without the structure: `f : Fin 10 × Fin 10 → Fin 10 × Fin 10` injective (so all 100 symbol pairs occur exactly once), and the first and second symbol functions injective along each row and each column.
--
--   **Why this is a variation.** Variation on the open MOLS.existence (a pair of mutually orthogonal Latin squares exists exactly for n not 2 or 6). It is the single case n = 10, with the parent's structure fields written out; a finite explicit certificate (a 10x10 Graeco-Latin square) settles it.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   R. C. Bose, S. S. Shrikhande and E. T. Parker, Further results on the construction of mutually orthogonal Latin squares and the falsity of Euler's conjecture, Canad. J. Math. 12 (1960) 189-203 (DOI 10.4153/CJM-1960-017-2; the title, journal and year verified by web search, page range cited from memory): a pair of orthogonal Latin squares exists for every order n other than 2 and 6. Origin: platform theorem MOLS.existence (Open), case n = 10.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- A pair of orthogonal Latin squares of order `10` exists, with the parent's `MOLS 10` fields written
out: a map `f` from cells to (symbol of square 1, symbol of square 2), injective (orthogonality), and
injective along every row and every column in each coordinate (Latin property). -/
theorem mols_exists_order_10 :
    ∃ f : Fin 10 × Fin 10 → Fin 10 × Fin 10,
      Function.Injective f ∧
      (∀ r, Function.Injective fun c => (f (r, c)).1) ∧
      (∀ r, Function.Injective fun c => (f (r, c)).2) ∧
      (∀ c, Function.Injective fun r => (f (r, c)).1) ∧
      (∀ c, Function.Injective fun r => (f (r, c)).2) := by
  sorry

end LefebvreVariations
