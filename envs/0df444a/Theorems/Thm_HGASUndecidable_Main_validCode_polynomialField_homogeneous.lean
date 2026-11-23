-- Prove2me | Theorems.Thm_HGASUndecidable_Main_validCode_polynomialField_homogeneous
-- name    : HGASUndecidable.Main.validCode_polynomialField_homogeneous
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:49:31.187746+00:00
-- url     : https://prove2.me/theorems/616f9e77-1c7c-40a5-91e8-5b171bc9e4e1
-- title:
--   A valid finite code denotes a homogeneous polynomial vector field
-- statement:
--   Let $c$ be a valid raw field code, with declared dimension $n$ and declared degree $d$. The vector field denoted by the code is a polynomial vector field on $\mathbb R^n$ and is homogeneous of degree $d$ under positive scalar dilation.
--
--   This connects the finite-code semantics with the analytic hypotheses of the degree-reduction and padding constructions. It uses the normalized-support condition in code validity: after duplicate monomials are combined, every surviving monomial in every coordinate has total degree $d$. Zero coordinates and invalid codes are treated separately by the definitions.
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), finite-code semantics in Section 3.4 and its use in the proofs of Theorem 2.1 and Lemma 6.1, printed pp. 16 and 35 (PDF 18 and 37).

import Definitions.Def_HGASUndecidable_Main_Codes

open Filter Topology MeasureTheory
open scoped BigOperators

theorem HGASUndecidable.Main.validCode_polynomialField_homogeneous
    (c : HGASUndecidable.Main.RawFieldCode) (hc : HGASUndecidable.Main.ValidCode c) :
    HGASUndecidable.Main.PolynomialField (HGASUndecidable.Main.codeField c) ∧
      HGASUndecidable.Main.Homogeneous c.2.1 (HGASUndecidable.Main.codeField c) := by sorry
