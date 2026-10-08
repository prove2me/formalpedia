-- Prove2me | Theorems.Thm_FriezeKannan_CutDecomp_theorem_7
-- name    : FriezeKannan.CutDecomp.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:59.863654+00:00
-- url     : https://prove2.me/theorems/d53aa5fa-2fb9-408b-b1a7-f7344ed0f8ac
-- title:
--   Theorem 7, p. 188 — every real matrix is a sum of s ≤ 1/ε² cut matrices plus W with |W(S,T)| ≤ ε√(|S||T|)‖A‖_F
-- statement:
--   Let $A$ be a real $m\times n$ matrix with rows indexed by $R$ and columns by $C$, and let $\varepsilon>0$. Then there are $s\le 1/\varepsilon^2$ cut matrices $D^{(t)}=\mathrm{CUT}(R_t,C_t,d_t)$, $t=1,\dots,s$, with $R_t\subseteq R$, $C_t\subseteq C$ and $d_t\in\mathbb R$, such that the error $W^{(s)}=A-(D^{(1)}+\dots+D^{(s)})$ satisfies
--   $$|W^{(s)}(S,T)|\le\varepsilon\sqrt{|S|\,|T|}\;\|A\|_F\qquad\text{for all }S\subseteq R,\ T\subseteq C. \tag{17}$$
--
--   This is the non-constructive form of Frieze and Kannan's weak regularity lemma for matrices: any real matrix is approximated, uniformly over all rectangles and in the scale-correct form $\sqrt{|S||T|}\|A\|_F$, by a sum of a number of rank-one block matrices that depends on $\varepsilon$ alone and not on the dimensions. The algorithmic decompositions and the applications to dense Max-Cut and pseudo-regular partitions of the paper build on it.
--
--   **Formalization Note** The paper leaves the range of $\varepsilon$ implicit (its error parameters lie in $(0,1)$); $\varepsilon>0$ is assumed, and $\varepsilon<1$ is not needed. $s=0$ (no cut matrix) is allowed. The cut matrices are arbitrary: no nonemptiness, disjointness or sign condition is imposed on $R_t$, $C_t$, $d_t$. The width bound $s\le 1/\varepsilon^2$ is the content of the theorem: without it, one cut matrix per entry gives $W=0$.
-- source:
--   Frieze and Kannan, Quick approximation to matrices and applications, Combinatorica 19 (1999), p. 188, Theorem 7 and (17)

import Mathlib
import Definitions.Def_FriezeKannan_CutDecomp_Setting

namespace FriezeKannan.CutDecomp

/-- Theorem 7, p. 188: every real `R × C` matrix `A` is a sum of at most `1/ε²` cut matrices
`CUT(R_t, C_t, d_t)` plus a remainder `W^(s)` with
`|W^(s)(S, T)| ≤ ε √(|S| |T|) ‖A‖_F` for all `S ⊆ R`, `T ⊆ C` (17). -/
theorem theorem_7 {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℕ, (s : ℝ) ≤ 1 / ε ^ 2 ∧
      ∃ (Rs : Fin s → Finset R) (Cs : Fin s → Finset C) (d : Fin s → ℝ),
        ∀ (S : Finset R) (T : Finset C),
          |blockSum (A - cutSum Rs Cs d) S T|
            ≤ ε * Real.sqrt ((S.card : ℝ) * T.card) * frobNorm A := by sorry

end FriezeKannan.CutDecomp
