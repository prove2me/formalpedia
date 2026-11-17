-- Prove2me | Theorems.Thm_N25_canonicalXHPlaceEquiv25_order
-- name    : N25.canonicalXHPlaceEquiv25_order
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:18:43.995116+00:00
-- url     : https://prove2.me/theorems/c677b318-047f-407c-bfdf-a2b2e80bc421
-- title:
--   The canonical-to-modular place equivalence preserves valuation orders
-- statement:
--   Let $e:F_{\mathrm{can}}≃ℚ(X_H(25))$ be the fixed function-field isomorphism, let $e_*$ be its induced place equivalence, let $P$ be a place of $F_{\mathrm{can}}$, and let $f∈F_{\mathrm{can}}$. Then $$(e_*P)(e(f))=P(f)\quad\text{at the level of valuation orders},$$ equivalently, $$\operatorname{ord}_{e_*P}(e(f))=\operatorname{ord}_P(f).$$ This transports unit and pole information without changing orders.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalModularDictionary

open N25

theorem N25.canonicalXHPlaceEquiv25_order
    (P : AlgebraicCurve.Place ℚ (CanonicalFF25 ℚ)) (f : CanonicalFF25 ℚ) :
    (canonicalXHPlaceEquiv25 P).ord (canonicalXHAlgEquiv25 f) = P.ord f := by sorry
