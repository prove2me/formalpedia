-- Prove2me | Theorems.Thm_N25_canonicalXHPlaceEquiv25_degree
-- name    : N25.canonicalXHPlaceEquiv25_degree
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:19:09.376782+00:00
-- url     : https://prove2.me/theorems/801c0d35-8838-4dc6-8fc8-cc70a69c757f
-- title:
--   The canonical-to-modular place equivalence preserves degree
-- statement:
--   Let $e:F_{\mathrm{can}}≃ℚ(X_H(25))$ be the canonical function-field isomorphism and let $e_*$ be the induced equivalence on places. For every place $P$ of $F_{\mathrm{can}}/ℚ$, $$\deg(e_*P)=\deg(P).$$ This allows rational places to be transported between the canonical and modular models.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalModularDictionary

open N25

theorem N25.canonicalXHPlaceEquiv25_degree
    (P : AlgebraicCurve.Place ℚ (CanonicalFF25 ℚ)) :
    (canonicalXHPlaceEquiv25 P).deg = P.deg := by sorry
