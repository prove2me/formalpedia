-- Prove2me | Theorems.Thm_Kyprianou_Ch06_disjointMarkTimeProductCompatible
-- name    : Kyprianou.Ch06.disjointMarkTimeProductCompatible
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:18:21.092303+00:00
-- url     : https://prove2.me/theorems/4d00ecea-bd7b-43e1-8628-ff8b739372d3
-- title:
--   Lemma 6.18: compatibility of product rectangles from disjoint marks and separated times
-- statement:
--   If any two different marks in a finite family are disjoint and the finite time intervals are pairwise separated, then the Cartesian-product rectangles indexed by Fin(a*k) satisfy the marked-Poisson compatibility condition: each pair is time-separated or has disjoint mark supports. This is the structural product step in the full compatible-rectangle representation for Lemma 6.18.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), printed pp.160–161, finite compatible mark-time rectangles.

import Mathlib
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.disjointMarkTimeProductCompatible
    {E : Type} (a k : Nat) (marks : Fin a → Set E)
    (hDisjoint : ∀ i j : Fin a, i ≠ j →
      Disjoint (marks i) (marks j))
    (starts stops : Fin k → NNReal)
    (hTimes : ∀ i j : Fin k, i ≠ j →
      stops i ≤ starts j ∨ stops j ≤ starts i)
    (p q : Fin (a * k)) (hpq : p ≠ q) :
    let e : Fin (a * k) ≃ Fin a × Fin k := finProdFinEquiv.symm
    stops (e p).2 ≤ starts (e q).2 ∨
    stops (e q).2 ≤ starts (e p).2 ∨
    Disjoint (marks (e p).1) (marks (e q).1) := by sorry
