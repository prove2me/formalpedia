-- Prove2me | Theorems.Thm_MulticlassDS_NatGap_cor44_no_empty_square_natarajan_le_one
-- name    : MulticlassDS.NatGap.cor44_no_empty_square_natarajan_le_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:49:21.57521+00:00
-- url     : https://prove2.me/theorems/70a546fc-6544-49dc-8811-f6812a9f7d19
-- title:
--   Corollary 44, p. 29 — no empty squares in a good complex C gives d_N(B(C, r)) ≤ 1 for every proper coloring r
-- statement:
--   Let $C$ be a good simplicial complex of dimension $d$ over $V$ that contains no empty square. Then for every proper coloring $r$ of $C$,
--   $$d_N\big(B(C, r)\big) \le 1 .$$
--
--   This is the coloring-free version of Proposition 43: the absence of empty squares is a property of the complex alone, and it bounds the Natarajan dimension of every pseudo-cube the complex defines.
--
--   **Formalization Note** $B(C,r)$ is a class over `Fin (d + 1)`; the dimension is $\mathbb N_\infty$-valued.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 29, Corollary 44

import Mathlib
import Definitions.Def_MulticlassDS_NatGap_Dimensions
import Definitions.Def_MulticlassDS_NatGap_Complexes

namespace MulticlassDS.NatGap

theorem cor44_no_empty_square_natarajan_le_one {V : Type*} (C : Set (Finset V)) (d : ℕ)
    (hC : IsGood C d) (hsq : NoEmptySquares C) :
    ∀ r : V → Fin (d + 1), IsProperColoring C d r →
      natarajanDim (pseudoCubeOf C d r) ≤ 1 := by sorry

end MulticlassDS.NatGap
