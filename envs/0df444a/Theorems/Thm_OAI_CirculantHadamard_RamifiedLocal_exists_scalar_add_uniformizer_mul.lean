-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_RamifiedLocal_exists_scalar_add_uniformizer_mul
-- name    : OAI.CirculantHadamard.RamifiedLocal.exists_scalar_add_uniformizer_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:23:41.377983+00:00
-- url     : https://prove2.me/theorems/1ecc8cf1-772d-4719-bb06-ff6802072c8b
-- title:
--   Every element is a scalar plus a multiple of zeta minus one
-- statement:
--   Let $A$ be a commutative ring, $p,k\in\mathbb N$, and $E=A[X]/(\Phi_{p^{k+1}}(X))$ with root $\zeta$ and $\pi=\zeta-1$. Every $x\in E$ can be written as
--   $$
--   x=a+\pi\,b\qquad(a\in A,\ b\in E).
--   $$
--
--   Modulo $\pi$, every element of the ramified extension is congruent to a scalar from the base.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/RamifiedLocal.lean#L42-L63

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

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.RamifiedLocal
universe uA
open Polynomial

theorem OAI.CirculantHadamard.RamifiedLocal.exists_scalar_add_uniformizer_mul (A : Type uA) [CommRing A] (p k : ℕ)
    (x : Extension A p k) :
    ∃ a : A, ∃ b : Extension A p k,
      x = algebraMap A (Extension A p k) a + uniformizer A p k * b := by sorry
