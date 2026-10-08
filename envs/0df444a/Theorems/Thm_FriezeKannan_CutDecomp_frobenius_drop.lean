-- Prove2me | Theorems.Thm_FriezeKannan_CutDecomp_frobenius_drop
-- name    : FriezeKannan.CutDecomp.frobenius_drop
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:43.997908+00:00
-- url     : https://prove2.me/theorems/5f2b6324-c923-4b32-88cf-74dfdbc38bc1
-- title:
--   §4.1, proof of Theorem 7, p. 188 — ‖W − CUT(S,T,d)‖²_F − ‖W‖²_F = −|S||T|d² = −W(S,T)²/(|S||T|) for d = W(S,T)/(|S||T|)
-- statement:
--   Let $W$ be a real $R\times C$ matrix and let $S\subseteq R$, $T\subseteq C$ be nonempty. Put
--   $$d=\frac{W(S,T)}{|S|\,|T|},$$
--   the average entry of $W$ on the rectangle $S\times T$, and let $D=\mathrm{CUT}(S,T,d)$. Then
--   $$\|W-D\|_F^2-\|W\|_F^2=\sum_{i\in S,\ j\in T}\big((W(i,j)-d)^2-W(i,j)^2\big)=-|S|\,|T|\,d^2=-\frac{W(S,T)^2}{|S|\,|T|}.$$
--
--   Subtracting from $W$ its average on a rectangle therefore lowers the squared Frobenius norm by exactly $W(S,T)^2/(|S||T|)$. This is the energy-decrement computation that drives the existence proof of cut decompositions (Theorem 7).
--
--   **Formalization Note** $S$ and $T$ are assumed nonempty, as in the paper, where they come from a rectangle with $W(S,T)\ne 0$; this keeps the division defining $d$ meaningful. All three equalities of the display are stated.
-- source:
--   Frieze and Kannan, Quick approximation to matrices and applications, Combinatorica 19 (1999), p. 188, §4.1, proof of Theorem 7 (displayed computation of ‖W^(t+1)‖²_F − ‖W‖²_F)

import Mathlib
import Definitions.Def_FriezeKannan_CutDecomp_Setting

namespace FriezeKannan.CutDecomp

/-- §4.1, proof of Theorem 7, p. 188: subtracting `CUT(S, T, d)` with
`d = W(S, T)/(|S||T|)` lowers `‖W‖²_F` by exactly `|S||T| d² = W(S, T)²/(|S||T|)`. -/
theorem frobenius_drop {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (W : Matrix R C ℝ) (S : Finset R) (T : Finset C) (hS : S.Nonempty) (hT : T.Nonempty) :
    let d : ℝ := blockSum W S T / ((S.card : ℝ) * T.card)
    (frobNorm (W - cutMatrix S T d) ^ 2 - frobNorm W ^ 2
        = ∑ i ∈ S, ∑ j ∈ T, ((W i j - d) ^ 2 - W i j ^ 2)) ∧
      (frobNorm (W - cutMatrix S T d) ^ 2 - frobNorm W ^ 2
        = -((S.card : ℝ) * T.card) * d ^ 2) ∧
      (frobNorm (W - cutMatrix S T d) ^ 2 - frobNorm W ^ 2
        = -(blockSum W S T) ^ 2 / ((S.card : ℝ) * T.card)) := by sorry

end FriezeKannan.CutDecomp
