-- Prove2me | Theorems.Thm_LefebvreVariations_hadwiger_covering_plane
-- name    : LefebvreVariations.hadwiger_covering_plane
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:51:56.559861+00:00
-- url     : https://prove2.me/theorems/54df198c-8f7d-53fc-a1cb-bb9854e4a2b5
-- title:
--   Lefebvre's variations, No. 110 — on a theme by Hadwiger: covering a planar convex body by four smaller copies
-- statement:
--   Let $K\subset\mathbb{R}^2$ be a compact convex set with non-empty interior. Then there exist four points $c_1,\dots,c_4$ and ratios $0<r_1,\dots,r_4<1$ with
--   $$
--   K\;\subseteq\;\bigcup_{i=1}^{4}\big(c_i+r_iK\big).
--   $$
--
--   This is the planar case of the Hadwiger covering (Levi–Hadwiger–Gohberg–Markus) conjecture: every convex body of $\mathbb{R}^d$ can be covered by $2^d$ smaller homothetic copies of itself. In the plane the conjecture is a theorem of Levi (four copies, three suffice unless $K$ is a parallelogram); it is open for every $d\ge 3$.
--
--   **Formalization Note** `K : Set (EuclideanSpace ℝ (Fin 2))` with `IsCompact K`, `Convex ℝ K` and `(interior K).Nonempty`. The homothetic copies are the images `(fun x => c i + r i • x) '' K` with `0 < r i < 1`; the union is over `i : Fin 4`. Only an upper bound of four copies is asserted, repeated or unneeded copies are allowed.
--
--   **Why this is a variation.** Special case d = 2 of the Hadwiger covering conjecture (every convex body of R^d is covered by 2^d smaller homothetic copies). It is a classical theorem of Levi; the conjecture is open for every d >= 3. No entry for the conjecture was found on the platform by keyword search, so there is no platform parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent (mathematical): the Hadwiger covering (Levi-Hadwiger-Gohberg-Markus) conjecture; no platform entry found by keyword search. This is the case d = 2, a theorem of F. W. Levi.
--   Source (cited from memory, not verified): F. W. Levi, 'Ueberdeckung eines Eibereiches durch Parallelverschiebung seines offenen Kerns', Arch. Math. 6 (1955), 369-370; search also surfaced Levi, 'Ein geometrisches Ueberdeckungsproblem', Arch. Math. 5 (1954), 476-478, which may be the intended reference. The claim that three copies suffice unless K is a parallelogram is cited from memory.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Levi's theorem, the planar case of the Hadwiger covering conjecture: every planar convex body
is covered by four homothetic copies of ratio strictly between 0 and 1. -/
theorem hadwiger_covering_plane (K : Set (EuclideanSpace ℝ (Fin 2)))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hint : (interior K).Nonempty) :
    ∃ (c : Fin 4 → EuclideanSpace ℝ (Fin 2)) (r : Fin 4 → ℝ),
      (∀ i, 0 < r i ∧ r i < 1) ∧
      K ⊆ ⋃ i, (fun x => c i + r i • x) '' K := by
  sorry

end LefebvreVariations
