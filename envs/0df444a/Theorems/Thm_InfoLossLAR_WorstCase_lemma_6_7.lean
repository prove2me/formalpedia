-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_lemma_6_7
-- name    : InfoLossLAR.WorstCase.lemma_6_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:03:52.660809+00:00
-- url     : https://prove2.me/theorems/43966858-2f27-43ed-9271-242be3245f55
-- title:
--   Lemma 6.7 — $|\det[D_{\mathscr T}\mid v]|=|\mathbf 1^\top v|$ for an oriented tree
-- statement:
--   For every oriented tree $\mathscr T$ on $d$ vertices with signed incidence matrix $D_{\mathscr T}\in\mathbb Z^{d\times(d-1)}$ and every integer column $v\in\mathbb Z^d$,
--   $$|\det[D_{\mathscr T}\mid v]|=|\mathbf 1^\top v| .$$
--
--   Differences from the source:
--   - encoding: the $d$ columns of $[D_{\mathscr T}\mid v]$ in the paper's order → in an arbitrary order given by a bijection $\sigma$ from (edges $\sqcup$ one extra column) to $\{1,\dots,d\}$; reason: $|\det|$ does not depend on the column order, and the paper does not fix one
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 28, Lemma 6.7

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_FixedT

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

/-- Lemma 6.7 (Determinant of an extended tree incidence matrix), p. 28: for every oriented
tree `𝒯` on the `d` vertices `Fin d` and every `v ∈ ℤ^d`, `|det[D_𝒯 | v]| = |1ᵀv|`. The `d`
columns (the `d − 1` edge columns and `v`) are put in an arbitrary order `σ`; the absolute value
of the determinant does not depend on it. -/
theorem lemma_6_7 (d : ℕ) (𝒯 : OrientedTree d) (v : Fin d → ℤ)
    (σ : 𝒯.G.edgeSet ⊕ Unit ≃ Fin d) :
    |((𝒯.extended v).submatrix id σ.symm).det| = |∑ i, v i| := by sorry

end InfoLossLAR.WorstCase
