-- Prove2me | Theorems.Thm_LinearChoresCLS_completedRatMarket_from_metadata
-- name    : LinearChoresCLS.completedRatMarket_from_metadata
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T04:00:25.144529+00:00
-- url     : https://prove2.me/theorems/aab101be-6e63-4a3a-b398-d7e4653ea919
-- title:
--   Serialize the explicit completed market from source data and chain-length metadata
-- statement:
--   There is one polynomial-time Cook-machine serializer $g$ with the following behavior. Let $P$ be a quadratic source instance of dimension $n\ge1$, let $\varepsilon>0$ be rational, and let $L$ be its prescribed chain length $L(P,\varepsilon)$ from equation (7.1). On the tagged pair consisting of the metadata word $\operatorname{encNat}(n)\,\|\,\operatorname{encNat}(L)$ and the original source word $\operatorname{enc}(P)\,\|\,\operatorname{enc}(\varepsilon)$, the serializer outputs the exact binary encoding of the canonical rational completed market:
--   $$
--   g\bigl((\operatorname{encNat}(n),\operatorname{encNat}(L))\,\#\,(P,\varepsilon)\bigr)
--    =\operatorname{encChores}(\operatorname{completedRatMarket}(P,\varepsilon)).
--   $$
--
--   This isolates the explicit construction in Section 7.1(i)–(iv): enumerate the basic and gadget agents and chores, evaluate the rational disutilities, earning requirements and supplies using $t=2^{-L}$, and write the resulting matrix and vectors. The chain-length search itself is deliberately not part of this serializer; it is supplied by the preceding source-parameter computation. Behavior on malformed tagged pairs is unconstrained.
--
--   **Formalization Note** Polynomial time means `CookPvsNP.PolyTimeComputable` on total word functions. The tagged input uses the public `pairCode` alphabet `Option (Bool ⊕ Bool)`, and the equality $L=L(P,\varepsilon)$ is an explicit validity hypothesis.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Section 7, equation (7.1), p.30; Section 7.1 (i)–(iv), p.31; and the polynomial-time market construction statement, p.32. Auxiliary decomposition isolating serialization after computation of n and L.

import Definitions.Def_LinearChoresCLS_EncodedMarket

open NetworkEquilibriumCLS.LinearNash LinearChoresCLS

theorem LinearChoresCLS.completedRatMarket_from_metadata :
    ∃ g : List (Option (Bool ⊕ Bool)) → List Bool, PolyTime g ∧
      ∀ {n : ℕ}, 0 < n → ∀ (L : ℕ) (P : Quadratic n) (ε : ℚ),
        0 < ε → L = chainLength P ε →
        encChores (completedRatMarket P ε) =
          g (pairCode (encNat n ++ encNat L) (encQuadratic P ++ encRat ε)) := by sorry
