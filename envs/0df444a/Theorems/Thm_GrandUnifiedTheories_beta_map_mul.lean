-- Prove2me | Theorems.Thm_GrandUnifiedTheories_beta_map_mul
-- name    : GrandUnifiedTheories.beta_map_mul
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T00:52:26.134904+00:00
-- url     : https://prove2.me/theorems/c59b9b23-53ee-42d1-a3b6-74dda3402d15
-- title:
--   $\beta$ is a group homomorphism
-- statement:
--   The Pati-Salam map $\beta$ is multiplicative: for all $x, y\in G_{\mathrm{SM}}$,
--
--   $$\beta(xy) \;=\; \beta(x)\,\beta(y),$$
--
--   where the right-hand side is the componentwise product in $\mathrm{SU}(2)\times\mathrm{SU}(2)\times\mathrm{SU}(4)$, each component being a product of matrices of the appropriate size.
--
--   With the previous milestone this makes $\beta$ a homomorphism of Lie groups $G_{\mathrm{SM}}\to\mathrm{SU}(2)\times\mathrm{SU}(2)\times\mathrm{SU}(4)$, so that pulling the Pati-Salam representation back along $\beta$ is meaningful.
-- source:
--   John Baez and John Huerta, The Algebra of Grand Unified Theories, https://math.ucr.edu/home/baez/guts.pdf, Section 3.3, p. 54 (the displayed map β, used as a Lie group homomorphism in Theorem 3, p. 55)

import Mathlib
import Definitions.Def_GUT_standard_model_group

namespace GrandUnifiedTheories

theorem beta_map_mul (x y : GSM) :
    betaMatrix (x * y) =
      ((betaMatrix x).1 * (betaMatrix y).1,
        (betaMatrix x).2.1 * (betaMatrix y).2.1,
        (betaMatrix x).2.2 * (betaMatrix y).2.2) := by sorry

end GrandUnifiedTheories
