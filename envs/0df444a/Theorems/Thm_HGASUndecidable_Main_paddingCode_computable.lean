-- Prove2me | Theorems.Thm_HGASUndecidable_Main_paddingCode_computable
-- name    : HGASUndecidable.Main.paddingCode_computable
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:24:33.492798+00:00
-- url     : https://prove2.me/theorems/918bcda8-d2b0-49a7-86a2-efa6b65e40a4
-- title:
--   Explicit polynomial padding code is computable
-- statement:
--   For fixed $m\le n$ and $j$, the map from the cubic input coefficient list to the canonical encoding of the finite coefficient list of $(\sum_{k<n}x_k^2)^j\,F(x,0,\ldots,0,-x_{m+1}^3,\ldots,-x_n^3)$ is computable. The proof is by explicit finite exponent arithmetic, `MvPolynomial.toSymDegrees`, sorting, and pairing/encoding; no noncomputable real-number operation is part of the construction.
-- source:
--   Paper #1477, Lemma 6.1 (printed p. 15/PDF 17), Algorithm step (ii) in the proof of Theorem 2.1 (printed p. 11/PDF 13): padding is an effective substitution and multiplication of rational polynomials.

import Definitions.Def_HGASUndecidable_Main_PaddingCodes

theorem HGASUndecidable.Main.paddingCode_computable {m n : ℕ} (h : m ≤ n) (j : ℕ) :
    Computable (HGASUndecidable.Main.paddingCode h j) := by sorry
