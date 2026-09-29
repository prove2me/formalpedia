-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_rephasingEquiv_entry
-- name    : KobayashiMaskawa1973.rephasingEquiv_entry
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:28:45.256987+00:00
-- url     : https://prove2.me/theorems/1dfe3250-b0dd-4ff6-b565-899aafecb966
-- title:
--   Entries of a rephased matrix are scaled by row and column phase factors
-- statement:
--   For any $3 \times 3$ complex matrix $U$ and diagonal phase matrices $D(a) = \operatorname{diag}(e^{ia})$, $D(b) = \operatorname{diag}(e^{ib})$ with real vectors $a, b \in \mathbb{R}^3$, the entries of the rephased matrix $V = D(a) U D(b)$ satisfy:
--
--   $$V_{ij} = e^{i a_i} U_{ij} e^{i b_j}$$
--
--   for all indices $i, j \in \{0, 1, 2\}$.
-- source:
--   Definitions.Def_KobayashiMaskawa1973_Defs

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem rephasingEquiv_entry (U V : Matrix (Fin 3) (Fin 3) ℂ) (a b : Fin 3 → ℝ) (h : phaseDiag a * U * phaseDiag b = V) (i j : Fin 3) :
    V i j = Complex.exp ((a i : ℂ) * Complex.I) * U i j * Complex.exp ((b j : ℂ) * Complex.I) := by sorry

end KobayashiMaskawa1973
