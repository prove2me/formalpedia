-- Prove2me | Theorems.Thm_LinearChoresCLS_unary_to_epsQKKT_reduction
-- name    : LinearChoresCLS.unary_to_epsQKKT_reduction
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:46:01.719236+00:00
-- url     : https://prove2.me/theorems/8ace0d6d-6d9b-4890-88f6-10f24493a127
-- title:
--   Exact unary quadratic KKT reduces to $\varepsilon$-quadratic KKT
-- statement:
--   Exact quadratic box-KKT on the public unary rational input encoding reduces in polynomial time to the $\varepsilon$-quadratic-KKT problem:
--   $$
--   \operatorname{unaryQuadraticKKT}\le_p \varepsilon\text{-quadratic-KKT}.
--   $$
--   The intended reduction maps an exact instance $P$ to an approximate instance for $-P$, with the sufficiently small rational tolerance supplied by the quadratic-KKT rounding lemma. Every approximate answer is rounded back to an exact KKT point of $P$; the decoder works for answers of arbitrary encoding length. Negating the coefficients converts the minimization KKT convention of the rounding interface into the maximization convention of Definition 2.4.
--
--   **Formalization Note** The source and target are the public `unarySearch` and `epsQKKTSearch`, and the reduction is the public all-answers `SearchReduces` relation on Cook machines.
-- source:
--   Fearnley–Goldberg–Hollender–Savani, The Complexity of Computing KKT Solutions of Quadratic Programs, Theorem 2.1 and Lemma A.1, as cited in Liu–Ma–Tao–Yang–Zheng, arXiv:2611.06589, Theorem 2.5, p.7; Anagnostides–Panageas–Yan STOC 2027 #653, Lemma 2.2, printed p.6 (PDF 7).

import Mathlib
import Definitions.Def_LinearChoresCLS_EpsKKT
import Definitions.Def_UnaryQuadraticKKT_Hardness_Input

open NetworkEquilibriumCLS.LinearNash

theorem LinearChoresCLS.unary_to_epsQKKT_reduction :
    NetworkEquilibriumCLS.LinearNash.SearchReduces UnaryQuadraticKKT.Hardness.unarySearch epsQKKTSearch := by sorry
