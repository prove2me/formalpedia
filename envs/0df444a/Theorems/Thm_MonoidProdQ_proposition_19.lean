-- Prove2me | Theorems.Thm_MonoidProdQ_proposition_19
-- name    : MonoidProdQ.proposition_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:50:46.019458+00:00
-- url     : https://prove2.me/theorems/ba7f20d5-a4ff-492c-923c-e7897a5eb7be
-- title:
--   Proposition 19: finite commutative aperiodic monoids are $\mathcal J$-, $\mathcal R$- and $\mathcal L$-trivial
-- statement:
--   Let $M$ be a finite commutative aperiodic monoid. Then $M$ is
--
--   1. $\mathcal J$-trivial: $MxM=MyM$ implies $x=y$;
--   2. $\mathcal R$-trivial: $xM=yM$ implies $x=y$;
--   3. $\mathcal L$-trivial: $Mx=My$ implies $x=y$.
--
--   This is the structural fact behind Lemma 20: in such a monoid an element is determined by the principal ideal it generates, so equal ideals force equal products.
--
--   Differences from the source: none.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Proposition 19, p.33

import Definitions.Def_MonoidProdQ_IsAperiodic
import Definitions.Def_MonoidProdQ_IsJTrivial
import Definitions.Def_MonoidProdQ_IsRTrivial
import Definitions.Def_MonoidProdQ_IsLTrivial

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Proposition 19, p.33: "A finite commutative aperiodic monoid is J-trivial (hence R-
and L-trivial)." All three conclusions are stated. -/
theorem proposition_19 {M : Type*} [CommMonoid M] [Finite M] (hM : IsAperiodic M) :
    IsJTrivial M ∧ IsRTrivial M ∧ IsLTrivial M := by sorry

end MonoidProdQ
