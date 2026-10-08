-- Prove2me | Theorems.Thm_MulticlassDS_NatGap_pseudo_cube_natarajan_one
-- name    : MulticlassDS.NatGap.pseudo_cube_natarajan_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:25:50.967791+00:00
-- url     : https://prove2.me/theorems/7d5ae4af-9dcf-491f-ac9a-98fb437ef4e6
-- title:
--   Proof of Theorem 2, p. 32 — for every d ≥ 1 there is a d-dimensional pseudo-cube with Natarajan dimension 1
-- statement:
--   For every integer $d \ge 1$ there are a label set $\mathcal Y_d$ and a $d$-dimensional pseudo-cube
--   $$B_d \subseteq \mathcal Y_d^{[d]}$$
--   whose Natarajan dimension is exactly $1$.
--
--   For $d = 2$ an example is the hexagon of Figure 1 of the paper (six words on six labels). The general case is the first step of the proof of Theorem 2: pseudo-cubes of every dimension that contain no copy of the Boolean square.
--
--   **Formalization Note** The page says "for every $d$"; at $d = 0$ the only $0$-dimensional pseudo-cube is the class containing the empty word, whose Natarajan dimension is $0$, so the statement is posed for $d \ge 1$. The derivation in the paper (Theorem 45, Proposition 46, Corollary 44) covers $d \ge 2$; the case $d = 1$ holds with $B_1 = \{0, 1\}^1$. The domain $X_d$ with $|X_d| = d$ is `Fin d`, and the label type is existentially quantified in `Type`.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 32, §5.4, proof of Theorem 2, first sentence

import Mathlib
import Definitions.Def_MulticlassDS_NatGap_Dimensions

namespace MulticlassDS.NatGap

theorem pseudo_cube_natarajan_one (d : ℕ) (hd : 1 ≤ d) :
    ∃ (Y : Type) (B : Set (Fin d → Y)), IsPseudoCube B ∧ natarajanDim B = 1 := by sorry

end MulticlassDS.NatGap
