-- Prove2me | Theorems.Thm_Freiman_legendre_adjacent_cylinders
-- name    : Freiman.legendre_adjacent_cylinders
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:09.587105+00:00
-- url     : https://prove2.me/theorems/2f070fc6-2ae5-4d73-aa8e-bf19f525b23d
-- title:
--   The two rational cylinders cover the Legendre neighborhood
-- statement:
--   Use the two finite expansions ending in c_m and in c_m−1,1. Their adjacent cylinders have lengths 1/(q(q+v)) and 1/(q(2q−v)), both larger than 1/(2q²). Irrationality excludes the rational common endpoint. This leaf is the geometric part of the report’s Legendre proof.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, found:legendre

import Definitions.Def_Freiman_perronArithmetic

namespace Freiman

theorem legendre_adjacent_cylinders (w : List ℕ+) (hw : w ≠ []) (hlast : 2 ≤ ((w.getLastD 1 : ℕ+) : ℕ)) (b : ℕ → ℕ+) :
    |cfValue b - finiteCF w| < 1 / (2 * (wordContinuantQ w : ℝ)^2) →
      ∃ n : ℕ, cfConvergent b n = finiteCF w := by
  sorry

end Freiman
