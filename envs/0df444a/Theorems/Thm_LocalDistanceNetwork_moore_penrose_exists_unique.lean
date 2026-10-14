-- Prove2me | Theorems.Thm_LocalDistanceNetwork_moore_penrose_exists_unique
-- name    : LocalDistanceNetwork.moore_penrose_exists_unique
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T20:29:53.304426+00:00
-- url     : https://prove2.me/theorems/d5782176-2b78-4656-b4c9-c4eb64db7ea2
-- title:
--   Penrose — every real matrix has a unique Moore–Penrose inverse
-- statement:
--   For every real matrix $M\in\mathbb R^{m\times k}$ there is exactly one matrix $P\in\mathbb R^{k\times m}$ satisfying the four Penrose equations
--   $$
--   MPM=M,\qquad PMP=P,\qquad (MP)^{\mathsf T}=MP,\qquad (PM)^{\mathsf T}=PM .
--   $$
--
--   This makes "the" Moore–Penrose inverse $M^{+}$ well defined, so that replacing $C^{-1}$ by $C^{+}$ in Eq. (B.1) for a singular covariance matrix $C$ is an unambiguous prescription.
-- source:
--   H0DN Collaboration (S. Casertano et al.), The Local Distance Network: A community consensus report on the measurement of the Hubble constant at ~1% precision, A&A 708, A166 (2026), https://doi.org/10.1051/0004-6361/202557993, Appendix B (p. 34) and Appendix B.2 (pp. 34-35), Eqs. (B.1)-(B.2)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS

open Matrix

namespace LocalDistanceNetwork
theorem moore_penrose_exists_unique {m k : Type*} [Fintype m] [Fintype k]
    (M : Matrix m k ℝ) :
    ∃! P : Matrix k m ℝ, IsMoorePenroseInverse M P := by sorry
end LocalDistanceNetwork
