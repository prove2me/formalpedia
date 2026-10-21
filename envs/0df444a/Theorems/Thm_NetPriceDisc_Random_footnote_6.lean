-- Prove2me | Theorems.Thm_NetPriceDisc_Random_footnote_6
-- name    : NetPriceDisc.Random.footnote_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:26.22786+00:00
-- url     : https://prove2.me/theorems/8276b832-2237-4a21-8daf-df4e5bc1c85a
-- title:
--   Footnote 6, p. 36 — a non-empty binary network has ‖G+Gᵀ‖ ≥ 1
-- statement:
--   Let $G$ be an $n\times n$ adjacency matrix with entries in $\{0,1\}$ and zero diagonal, with at least one link ($G\neq0$). Then
--   $$\|G+G^{\mathsf T}\|\ge1,$$
--   where $\|\cdot\|$ is the spectral norm.
--
--   In the proof of Theorem 5.1 (Appendix D.1, Case 1) this lets the factor $\|G+G^{\mathsf T}\|^{-2}$ in (29) be dropped for every non-empty sample network.
-- source:
--   Huang, Mani & Wang, The Value of Price Discrimination in Large Random Networks, SSRN 3368458 (EC '19 submission version), p. 36, Appendix D.1, Case 1, and footnote 6

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model
open Matrix

namespace NetPriceDisc.Random

theorem footnote_6 {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hbin : ∀ i j, G i j = 0 ∨ G i j = 1) (hdiag : ∀ i, G i i = 0) (hG0 : G ≠ 0) :
    1 ≤ specNorm (G + Gᵀ) := by sorry

end NetPriceDisc.Random
