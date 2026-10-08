-- Prove2me | Theorems.Thm_FriezeKannan_CutDecomp_frobenius_drop_le
-- name    : FriezeKannan.CutDecomp.frobenius_drop_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:42.289152+00:00
-- url     : https://prove2.me/theorems/bc15c429-0ef7-406e-b6ce-1cbd84df497c
-- title:
--   §4.1, proof of Theorem 7, p. 188 — if |W(S,T)| > ε√(|S||T|)‖A‖_F, removing the block average lowers ‖W‖²_F by at least ε²‖A‖²_F
-- statement:
--   Let $A$ and $W$ be real $R\times C$ matrices, let $\varepsilon>0$, and let $S\subseteq R$, $T\subseteq C$ be a rectangle on which (17) fails:
--   $$|W(S,T)|>\varepsilon\sqrt{|S|\,|T|}\;\|A\|_F .$$
--   (This forces $S$ and $T$ to be nonempty.) With $d=W(S,T)/(|S||T|)$,
--   $$\|W-\mathrm{CUT}(S,T,d)\|_F^2-\|W\|_F^2\le-\varepsilon^2\|A\|_F^2 .$$
--
--   Each rectangle that violates the target bound (17) thus buys a fixed decrease $\varepsilon^2\|A\|_F^2$ of the squared Frobenius norm of the error, which is what limits the number of cut matrices to $1/\varepsilon^2$ in Theorem 7.
--
--   **Formalization Note** The paper writes the violation as "$\ge$"; the negation of (17) is the strict "$>$", and with "$\ge$" the empty rectangle would qualify and $d$ would divide by zero, so the strict form is stated. The hypothesis $\varepsilon>0$ is the paper's standing range of the error parameter; some sign condition on $\varepsilon$ is needed, since for $\varepsilon<0$ the hypothesis holds for every rectangle with $W(S,T)\ne 0$ while the conclusion fails.
-- source:
--   Frieze and Kannan, Quick approximation to matrices and applications, Combinatorica 19 (1999), p. 188, §4.1, proof of Theorem 7 (last line of the display, ≤ −ε²‖A‖²_F)

import Mathlib
import Definitions.Def_FriezeKannan_CutDecomp_Setting

namespace FriezeKannan.CutDecomp

/-- §4.1, proof of Theorem 7, p. 188: if `|W(S, T)| > ε √(|S||T|) ‖A‖_F` then subtracting
`CUT(S, T, d)` with `d = W(S, T)/(|S||T|)` lowers `‖W‖²_F` by at least `ε² ‖A‖²_F`. -/
theorem frobenius_drop_le {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (A W : Matrix R C ℝ) (ε : ℝ) (hε : 0 < ε) (S : Finset R) (T : Finset C)
    (h : ε * Real.sqrt ((S.card : ℝ) * T.card) * frobNorm A < |blockSum W S T|) :
    frobNorm (W - cutMatrix S T (blockSum W S T / ((S.card : ℝ) * T.card))) ^ 2
        - frobNorm W ^ 2 ≤ -ε ^ 2 * frobNorm A ^ 2 := by sorry

end FriezeKannan.CutDecomp
