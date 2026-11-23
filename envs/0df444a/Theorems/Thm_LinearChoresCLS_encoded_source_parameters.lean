-- Prove2me | Theorems.Thm_LinearChoresCLS_encoded_source_parameters
-- name    : LinearChoresCLS.encoded_source_parameters
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:37:23.239812+00:00
-- url     : https://prove2.me/theorems/1cd62545-1ffa-4362-8df4-e0a180ceb9dc
-- title:
--   Polynomial-time extraction of the source dimension and chain length
-- statement:
--   There is a deterministic polynomial-time procedure which, given the binary encoding of a valid $\varepsilon$-quadratic-KKT source instance $(P,\varepsilon)$ of dimension $n\ge1$, returns the encodings of $n$ and of the chain length $L=L(P,\varepsilon)$ chosen for the completed chores market.
--
--   The parameter $L$ is the exponent specified by equation (7.1): $t=2^{-L}$ is the largest dyadic value permitted by the source-dependent accuracy threshold. This lemma isolates the source-parameter portion of the decoder in Section 7.1; its output can subsequently be paired with an encoded price-allocation pair.
--
--   **Formalization Note** Polynomial time means `CookPvsNP.PolyTimeComputable` on total Boolean-word functions. The concatenated output is `encNat n ++ encNat L`, and behavior on words that are not valid source encodings is unconstrained.
-- source:
--   Liu, Ma, Tao, Yang, and Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589v1, https://arxiv.org/html/2611.06589v1, Section 7.1, equation (7.1), pp.30–32: the chain length is computed from the source instance, has polynomially bounded encoding length, and the decoder first computes t (equivalently L) from I.

import Definitions.Def_LinearChoresCLS_PriceFamily
import Definitions.Def_LinearChoresCLS_ChoresSearch

open NetworkEquilibriumCLS.LinearNash LinearChoresCLS

theorem LinearChoresCLS.encoded_source_parameters :
    ∃ h : List Bool → List Bool, PolyTime h ∧
      ∀ {n : ℕ}, 0 < n → ∀ (P : Quadratic n) (ε : ℚ), 0 < ε →
        h (encQuadratic P ++ encRat ε) = encNat n ++ encNat (chainLength P ε) := by sorry
