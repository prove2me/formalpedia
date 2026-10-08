-- Prove2me | Theorems.Thm_FriezeKannan_CutDecomp_inductive_step
-- name    : FriezeKannan.CutDecomp.inductive_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:34.855434+00:00
-- url     : https://prove2.me/theorems/3889c273-69d9-4d62-9759-f542db7558da
-- title:
--   §4.1, proof of Theorem 7, p. 188 — if ‖W^(t)‖²_F ≤ (1 − ε²t)‖A‖²_F, either (17) holds or one more cut matrix keeps the invariant at t + 1
-- statement:
--   Let $A$ be a real $R\times C$ matrix and $\varepsilon>0$. Suppose cut matrices $D^{(j)}=\mathrm{CUT}(R_j,C_j,d_j)$, $j=1,\dots,t$, have been found such that the error $W^{(t)}=A-(D^{(1)}+\dots+D^{(t)})$ satisfies
--   $$\|W^{(t)}\|_F^2\le(1-\varepsilon^2 t)\,\|A\|_F^2 .$$
--   Then at least one of the following holds:
--   1. $W^{(t)}$ satisfies (17): $|W^{(t)}(S,T)|\le\varepsilon\sqrt{|S|\,|T|}\,\|A\|_F$ for all $S\subseteq R$, $T\subseteq C$;
--   2. there are $S\subseteq R$, $T\subseteq C$ and a real $d'$ such that
--   $$\|W^{(t)}-\mathrm{CUT}(S,T,d')\|_F^2\le\big(1-\varepsilon^2(t+1)\big)\,\|A\|_F^2 .$$
--
--   This is the inductive step of the existence proof of cut decompositions: the invariant $\|W^{(t)}\|_F^2\le(1-\varepsilon^2t)\|A\|_F^2$ cannot persist beyond $t=1/\varepsilon^2$, so the process stops with (17) after at most $1/\varepsilon^2$ cut matrices.
--
--   **Formalization Note** The paper also assumes $t<1/\varepsilon^2$; the step does not use it, and the statement is given without it. The family $D^{(1)},\dots,D^{(t)}$ is indexed by `Fin t` (so $t=0$, the empty family, is allowed), and the new cut matrix is added to their sum.
-- source:
--   Frieze and Kannan, Quick approximation to matrices and applications, Combinatorica 19 (1999), p. 188, §4.1, proof of Theorem 7 (inductive hypothesis ‖W‖²_F ≤ (1 − ε²t)‖A‖²_F and the dichotomy)

import Mathlib
import Definitions.Def_FriezeKannan_CutDecomp_Setting

namespace FriezeKannan.CutDecomp

/-- §4.1, proof of Theorem 7, p. 188: if the cut matrices `D^(1), …, D^(t)` leave a remainder
`W^(t) = A - (D^(1) + ⋯ + D^(t))` with `‖W^(t)‖²_F ≤ (1 - ε² t) ‖A‖²_F`, then either `W^(t)`
already satisfies (17), or one further cut matrix keeps the invariant with `t + 1`. -/
theorem inductive_step {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C ℝ) (ε : ℝ) (hε : 0 < ε) (t : ℕ)
    (Rs : Fin t → Finset R) (Cs : Fin t → Finset C) (d : Fin t → ℝ)
    (hinv : frobNorm (A - cutSum Rs Cs d) ^ 2 ≤ (1 - ε ^ 2 * t) * frobNorm A ^ 2) :
    (∀ (S : Finset R) (T : Finset C),
        |blockSum (A - cutSum Rs Cs d) S T|
          ≤ ε * Real.sqrt ((S.card : ℝ) * T.card) * frobNorm A) ∨
      ∃ (S : Finset R) (T : Finset C) (d' : ℝ),
        frobNorm (A - (cutSum Rs Cs d + cutMatrix S T d')) ^ 2
          ≤ (1 - ε ^ 2 * (t + 1)) * frobNorm A ^ 2 := by sorry

end FriezeKannan.CutDecomp
