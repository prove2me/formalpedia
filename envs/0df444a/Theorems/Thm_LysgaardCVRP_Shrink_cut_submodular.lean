-- Prove2me | Theorems.Thm_LysgaardCVRP_Shrink_cut_submodular
-- name    : LysgaardCVRP.Shrink.cut_submodular
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T16:51:28.292669+00:00
-- url     : https://prove2.me/theorems/845cfa05-7261-405c-9c8d-2bc3385d6d3a
-- title:
--   Submodularity of the cut function
-- statement:
--   Let $x \ge 0$ be a nonnegative edge vector on the complete graph with vertex set $V = \{0, \dots, n\}$. For any two vertex sets $S, T \subseteq V$,
--
--   $$x(\delta(T)) - x(\delta(S \cup T)) \ge x(\delta(S \cap T)) - x(\delta(S)).$$
--
--   Equivalently, $x(\delta(S \cup T)) + x(\delta(S \cap T)) \le x(\delta(S)) + x(\delta(T))$: the cut function of a nonnegatively weighted graph is submodular. The paper quotes this classical fact (Nemhauser and Wolsey, 1988, p. 660) in the proof of Proposition 1, in the arrangement displayed above.
--
--   **Formalization Note** Stated for arbitrary vertex sets, including sets containing the depot. Nonnegativity of $x$ is necessary.
-- source:
--   Lysgaard, Letchford & Eglese, A new branch-and-cut algorithm for the capacitated vehicle routing problem, Math. Program. Ser. A 100 (2004), p. 426 (PDF p. 4), proof of Proposition 1 (citing Nemhauser & Wolsey 1988, p. 660)

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut

namespace LysgaardCVRP.Shrink

/-- Submodularity of the cut function, in the arrangement used in the proof of Proposition 1 of
Lysgaard, Letchford & Eglese, *A new branch-and-cut algorithm for the capacitated vehicle
routing problem*, Math. Program. Ser. A 100 (2004), p. 426 (PDF p. 4) (unnumbered; the paper cites Nemhauser & Wolsey, *Integer and
Combinatorial Optimization*, 1988, p. 660): "It follows from the submodularity of the cut function
that $x^*(\delta(T)) - x^*(\delta(S\cup T)) \ge x^*(\delta(S\cap T)) - x^*(\delta(S))$".

**Formalization Note.** Stated for arbitrary vertex sets `S`, `T` of the complete graph on
`Fin (n+1)` (the fact does not need the depot condition; the paper applies it to customer sets),
and for a nonnegative edge vector $x \ge 0$ (the LP bounds of (3)–(4)); it is false for signed
$x$. -/
theorem cut_submodular {n : ℕ} (x : Sym2 (Fin (n + 1)) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (S T : Finset (Fin (n + 1))) :
    cut x T - cut x (S ∪ T) ≥ cut x (S ∩ T) - cut x S := by sorry

end LysgaardCVRP.Shrink
