-- Prove2me | Theorems.Thm_HGASUndecidable_Main_bounds94_exists
-- name    : HGASUndecidable.Main.bounds94_exists
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:47:43.363907+00:00
-- url     : https://prove2.me/theorems/892fd027-9683-4100-9fa2-9f316b09a7c3
-- title:
--   Lemma 9.4 — existence of the fixed rational bounds
-- statement:
--   For the valid fixed Diophantine system underlying Lemma 7.2, there exist rational constants $M_0\ge1$ and $K_0>0$, independent of $e$, with the quantitative properties of Lemma 9.4.
--
--   Writing $\rho_*$ for the fixed rational weight and $D_h$ for the degree of the test map $h_e$, define
--   $$
--   K_e=K_0\rho_*^{4D_h\lvert c(e)\rvert_1}.
--   $$
--   The constants supply a uniform bound $\lvert\Gamma_e\rvert^2\le M_0$, continuity and reality of the primitive $B_e$, the bound $\lvert B_e\rvert\le K_e$, its derivative identity along the linear torus flow, and vanishing of the constant Fourier coefficient of $h_e\circ\Gamma_e$ when $e\notin K$. Their numerical values need not be computed: they may occur as fixed constants in the program constructed in Theorem 2.3.
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), Lemma 9.4 and the paragraph following its proof, printed pp. 64–65 (PDF 66–67)

import Definitions.Def_HGASUndecidable_Main_Compactification

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

theorem bounds94_exists (a : DiophantineData) (ha : DiophantineValid a) :
    ∃ M₀ K₀ : ℚ, Bounds94 a M₀ K₀ := by sorry
