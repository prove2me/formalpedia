-- Prove2me | Theorems.Thm_HarmonicRanking_Main_finite_continuous_bound
-- name    : HarmonicRanking.Main.finite_continuous_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:35:47.532616+00:00
-- url     : https://prove2.me/theorems/21d52a91-72a1-4b07-9df6-077c577ff40e
-- title:
--   Proposition 5.2 — the finite flow lower-bounds the continuous game
-- statement:
--   For every $m\ge1$ and every positive nonincreasing real height vector $H$, let $h^{(m)}$ be its right-continuous step score. Then both inequalities hold:
--
--   $$
--   \gamma_{\rm EW}\ge\gamma_{\rm EW}(h^{(m)})\ge\operatorname{MF}_m(H).
--   $$
--
--   The family value is the supremum over the full source score class. The inner value uses all admissible measurable cutoff pairs, including curves that are not grid-aligned. This links finite flows to the unrestricted continuous variational target.
--
--   Differences from the source:
--   - encoding: cell indices 1 through m, threshold counts 0 through m → Fin m cell indices are shifted down by one and Fin (m+1) threshold counts are unchanged; reason: the same cells, adjacent arcs, and last-cell increments are represented bijectively
--   - encoding: measurable curves on [0,1] → a.e. measurable curves for Lebesgue law; reason: measurable representatives have the same payoffs and give the same variational value; no grid or curve monotonicity restriction is added
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 18, Proposition 5.2

import Definitions.Def_HarmonicRanking_Main_Network

set_option autoImplicit false

namespace HarmonicRanking.Main

theorem finite_continuous_bound {m : ℕ} (H : Fin m → ℝ) (hH : IsProfile H) :
    gammaEW (stepScore H) ≤ gammaFamily ∧ MF H ≤ gammaEW (stepScore H) := by sorry

end HarmonicRanking.Main
