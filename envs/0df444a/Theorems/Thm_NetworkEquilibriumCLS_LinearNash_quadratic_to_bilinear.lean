-- Prove2me | Theorems.Thm_NetworkEquilibriumCLS_LinearNash_quadratic_to_bilinear
-- name    : NetworkEquilibriumCLS.LinearNash.quadratic_to_bilinear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:49.966026+00:00
-- url     : https://prove2.me/theorems/a2b41849-810b-4d9b-a6c3-f726abf54e45
-- title:
--   Theorem 4.5 — full polynomial-time quadratic-to-bilinear KKT reduction
-- statement:
--   For all positive dimensions and explicitly supplied rational symmetric quadratic data, there is an all-answer polynomial-time search reduction
--
--   $$\mathrm{Quadratic\text{-}KKT}\le_p\mathrm{Bilinear\text{-}KKT}.$$
--
--   The source objective has no diagonal-normalization promise. The target has zero diagonal and may contain arbitrary linear terms. The instance map and decoder have uniform polynomial machine runtimes, and every exact rational target KKT point decodes to an exact rational source KKT point. This states the complete reduction, including its computational content, rather than an assumed reduction or a semantic existence correspondence.
--
--   Differences from the source:
--   - encoding: polynomial-time maps on explicitly supplied rational input → self-delimiting binary codes and the published Cook Turing-machine runtime, with a tagged input/answer pair for decoding; reason: one uniform machine and exponent are chosen before all instances; these codes are polynomially interconvertible with explicit binary lists
--   - generalization: normalization by positive scaling is performed before the construction → the source search relation retains all symmetric rational matrices; reason: positive rational scaling preserves all exact KKT points and can be carried out by the instance map; normalization is not imposed on the original input
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), p.14 (PDF 15), Theorem 4.5.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding

namespace NetworkEquilibriumCLS.LinearNash

/-- Source and every encoding convention are recorded in the item metadata. -/
theorem quadratic_to_bilinear :
    SearchReduces quadraticSearch bilinearSearch := by sorry

end NetworkEquilibriumCLS.LinearNash
