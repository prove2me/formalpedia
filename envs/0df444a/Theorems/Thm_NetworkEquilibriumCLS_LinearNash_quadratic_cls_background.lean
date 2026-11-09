-- Prove2me | Theorems.Thm_NetworkEquilibriumCLS_LinearNash_quadratic_cls_background
-- name    : NetworkEquilibriumCLS.LinearNash.quadratic_cls_background
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:01.322938+00:00
-- url     : https://prove2.me/theorems/ec760e05-25f7-4850-9989-5bd2dbc61d7d
-- title:
--   Background — exact quadratic box KKT is CLS-complete
-- statement:
--   Given a positive-dimensional symmetric rational Q and rational c, seek an exact rational box KKT point of p(z)=½zᵀQz+cᵀz on [0,1]^m, without convexity or diagonal normalization assumptions. With uniformly polynomial output encoding, this problem satisfies
--
--   $$\mathrm{Quadratic\text{-}KKT}\text{ is CLS-complete}.$$
--
--   Both membership and hardness are asserted for the fixed independently defined class. This is the external starting classification invoked in Section 2.1 and after Theorem 4.5, kept as a supporting theorem rather than a hypothesis of the goal.
--
--   Differences from the source:
--   - encoding: polynomial-time maps on explicitly supplied rational input → self-delimiting binary codes and the published Cook Turing-machine runtime, with a tagged input/answer pair for decoding; reason: one uniform machine and exponent are chosen before all instances; these codes are polynomially interconvertible with explicit binary lists
--   - encoding: polynomially encoded exact search answers → one exponent k chosen before all inputs, with total answer length at most (input length + 1)^k + k; reason: existence of k states the uniform polynomial output guarantee without inventing a numerical degree; totality and verification are conclusions inside CLS membership
--   - encoding: objective zᵀQz+cᵀz in the external source → objective ½zᵀQz+cᵀz; reason: multiply the explicitly supplied rational matrix by two; this is an invertible polynomial-time change of coefficient convention
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), p.6 (PDF 7), §2.1 background classification; Fearnley, Goldberg, Hollender and Savani, The Complexity of Computing KKT Solutions of Quadratic Programs (2025), arXiv:2311.13738v2, p.3 (PDF 4), Theorem (Main Result), unit-box clause, https://arxiv.org/pdf/2311.13738v2.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity

namespace NetworkEquilibriumCLS.LinearNash

/-- Supporting background result explicitly invoked by the source proof. -/
theorem quadratic_cls_background : ∃ k : ℕ, CLSComplete (bounded quadraticSearch k) := by sorry

end NetworkEquilibriumCLS.LinearNash
