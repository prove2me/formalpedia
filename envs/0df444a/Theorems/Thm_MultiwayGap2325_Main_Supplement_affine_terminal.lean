-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_terminal
-- name    : MultiwayGap2325.Main.Supplement.affine_terminal
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:55:27.135218+00:00
-- url     : https://prove2.me/theorems/237f0df4-751a-4ca0-8e1b-fcce47bd0ad5
-- title:
--   Terminal boundary condition for the affine flows
-- statement:
--   The affine data satisfy the terminal boundary condition for every $q\ge2$ and $T\in(1/2,1)$. On the terminal facet $\Phi_i^S$, where $x_i=T$, the normalized margin coordinate $p_i^S$ vanishes. Hence the $i$-component of the label-$\ell$ flow is $a_r$ when $\ell=i$ and is zero otherwise, exactly matching the prescribed terminal density $g_i^S=a_r$.
--
--   **Formalization Note** This is the pointwise terminal condition on every cell and every allowed label, as encoded by `TerminalCondition`.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), proof of Theorem 6.1, terminal-condition paragraph, p.23.

import Definitions.Def_MultiwayGap2325_Main_Supplement_AffineData

namespace MultiwayGap2325.Main.Supplement

/-- Theorem 6.1, p.23, terminal-condition paragraph. -/
theorem affine_terminal (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) :
    TerminalCondition T (affineData q T) := by sorry
