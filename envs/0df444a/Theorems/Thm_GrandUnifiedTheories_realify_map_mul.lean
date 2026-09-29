-- Prove2me | Theorems.Thm_GrandUnifiedTheories_realify_map_mul
-- name    : GrandUnifiedTheories.realify_map_mul
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T00:58:52.201236+00:00
-- url     : https://prove2.me/theorems/45b64882-a3dc-48b5-94b7-8c4ab63cdb31
-- title:
--   Realification is multiplicative
-- statement:
--   Writing each complex coordinate of $\mathbb{C}^5$ as a pair of real coordinates turns a complex $5\times5$ matrix $A$ into a real $10\times10$ matrix $\rho(A)$. This operation respects composition: for all complex $5\times5$ matrices $A$ and $B$,
--
--   $$\rho(AB) \;=\; \rho(A)\,\rho(B).$$
--
--   This is the statement that $\rho$ is the matrix form of "forget the complex structure": a complex-linear map and its underlying real-linear map compose the same way. It is the first of the three properties needed to view $\mathrm{SU}(5)$ as a subgroup of $\mathrm{SO}(10)$, as the proof of Theorem 8 does.
-- source:
--   John Baez and John Huerta, The Algebra of Grand Unified Theories, https://math.ucr.edu/home/baez/guts.pdf, Section 4, pp. 67-68 (proof of Theorem 8: 'if we forget the complex structure on ℂ⁵, we get an isomorphism ℂ⁵ ≅ ℝ¹⁰, a real inner product space with symmetries SO(10)')

import Mathlib
import Definitions.Def_GUT_standard_model_group
import Definitions.Def_GUT_realification

namespace GrandUnifiedTheories

theorem realify_map_mul (A B : Matrix Idx5 Idx5 ℂ) :
    realify (A * B) = realify A * realify B := by sorry

end GrandUnifiedTheories
