-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_DyadicRemainder_coefficientPolynomial_two_mul
-- name    : OAI.CirculantHadamard.DyadicRemainder.coefficientPolynomial_two_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:20:41.404355+00:00
-- url     : https://prove2.me/theorems/d2ed8090-c563-400f-83be-1a320e496edc
-- title:
--   Splitting a coefficient polynomial into two halves
-- statement:
--   For a commutative ring $R$, $c:\mathbb N\to R$ and $m\in\mathbb N$,
--   $$
--   \sum_{i<2m}c_iX^i=\sum_{i<m}c_iX^i+X^m\sum_{i<m}c_{i+m}X^i .
--   $$
--
--   The polynomial of length $2m$ is its lower block plus $X^m$ times its upper block, which is what makes reduction modulo $X^m+1$ subtract the upper block.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/DyadicRemainder.lean#L72-L88

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.DyadicRemainder
universe uR
open Polynomial Finset
variable {R : Type uR} [CommRing R]

theorem OAI.CirculantHadamard.DyadicRemainder.coefficientPolynomial_two_mul (m : ℕ) (c : ℕ → R) :
    coefficientPolynomial (2 * m) c = coefficientPolynomial m c +
      X ^ m * coefficientPolynomial m (fun i => c (i + m)) := by sorry
