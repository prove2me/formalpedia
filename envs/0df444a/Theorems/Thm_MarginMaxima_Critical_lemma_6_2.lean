-- Prove2me | Theorems.Thm_MarginMaxima_Critical_lemma_6_2
-- name    : MarginMaxima.Critical.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:03:10.65913+00:00
-- url     : https://prove2.me/theorems/69544edf-00f2-42f1-bc4f-aa7a5d25456e
-- title:
--   Lemma 6.2 — $a$ orthogonal copies of a zero-witness $\gamma$-shattered set are $(\gamma/\sqrt a)$-shattered
-- statement:
--   Suppose $m$ points of the unit ball are $\gamma$-shattered at zero witnesses by $r$-fold maxima of unit-norm functionals, and let $a\ge1$ be an integer. Then $am$ points are $(\gamma/\sqrt a)$-shattered at zero witnesses by $r$-fold maxima of unit-norm functionals.
--
--   Differences from the source:
--   - encoding: m points of the unit ball; am points → x : Fin m → Ball d; ∃ d′ and x′ : Fin (a·m) → Ball d′; reason: the dimension of the copies is not fixed by the lemma; points as sequences (shattered points are distinct for γ > 0)
--   - encoding: r-fold maxima of unit-norm functionals → MaxClass d r (heads of norm at most 1), 1 ≤ r; reason: 'Heads have norm at most 1' (p. 6); the proof's U_j has ∥U_j∥ ≤ 1
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 13, Lemma 6.2

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_MarginMaxima_Critical_MaxClass

namespace MarginMaxima.Critical

theorem lemma_6_2 (d m r a : ℕ) (hr : 1 ≤ r) (ha : 1 ≤ a) (γ : ℝ) (x : Fin m → Ball d)
    (hx : ZeroShatters (MaxClass d r) γ x) :
    ∃ (d' : ℕ) (x' : Fin (a * m) → Ball d'),
      ZeroShatters (MaxClass d' r) (γ / Real.sqrt a) x' := by sorry

end MarginMaxima.Critical
