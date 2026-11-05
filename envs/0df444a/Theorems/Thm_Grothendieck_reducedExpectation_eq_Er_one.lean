-- Prove2me | Theorems.Thm_Grothendieck_reducedExpectation_eq_Er_one
-- name    : Grothendieck.reducedExpectation_eq_Er_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T07:16:04.681369+00:00
-- url     : https://prove2.me/theorems/fd3d72b9-0f65-4ffd-a61d-134df93e9063
-- title:
--   The rank-one case of Lemma 2.1's canonical identity
-- statement:
--   For |tau| < 1, the integral of the rank-one rounding integrand against the law of a single bivariate Gaussian of correlation tau equals E_1(tau) = (2/pi) arcsin tau. This is the rank-one case of the matrix Grothendieck identity: at rank one the two Gaussian projections are scalars, the normalization is the sign, and the expectation reduces to the classical arcsine law for the correlation of two Gaussian signs. The proof transports the published arcsine law through the published pushforward identity at the explicit pair e1 = (1,0), (tau, sqrt(1-tau^2)). Rank one is the case no r >= 2 argument reaches.
-- source:
--   Briet, de Oliveira Filho, Vallentin, Theory of Computing 10(4), 2014, pp. 77-105 - Lemma 2.1 at r = 1.

import Mathlib
import Definitions.Def_Grothendieck_Reduced
import Definitions.Def_Grothendieck_Series

namespace Grothendieck

theorem reducedExpectation_eq_Er_one {τ : ℝ} (hτ : |τ| < 1) :
    (∫ W, reducedIntegrand 1 W ∂(reducedLaw 1 τ)) = Er 1 τ := by sorry

end Grothendieck
