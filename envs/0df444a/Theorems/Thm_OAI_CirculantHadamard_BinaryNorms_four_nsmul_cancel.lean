-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_BinaryNorms_four_nsmul_cancel
-- name    : OAI.CirculantHadamard.BinaryNorms.four_nsmul_cancel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:36:01.878754+00:00
-- url     : https://prove2.me/theorems/06b6fc7e-a383-40d1-aea9-2cb29ffa4189
-- title:
--   Cancelling a factor four in a group algebra
-- statement:
--   Let $R$ be a domain of characteristic zero and $f,g\in R[\mathbb Z/n]$. If
--   $$
--   4f=4g,
--   $$
--   then $f=g$.
--
--   Although the group algebra itself has zero divisors, multiplication by the scalar $4$ is injective because it acts coefficientwise.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/BinaryNorms.lean#L37-L53

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
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings

open OAI OAI.CirculantHadamard
universe uR uA
open CyclicRing
variable {R : Type uR} [CommRing R] [IsDomain R] [CharZero R]
variable {n : ℕ}

theorem OAI.CirculantHadamard.BinaryNorms.four_nsmul_cancel {f g : Elem R n}
    (h : (4 : ℕ) • f = (4 : ℕ) • g) : f = g := by sorry
