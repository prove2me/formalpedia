-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_RamifiedUnit_exists_polynomial_unit_factor
-- name    : OAI.CirculantHadamard.RamifiedUnit.exists_polynomial_unit_factor
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:21:14.978669+00:00
-- url     : https://prove2.me/theorems/9fc28540-b4fe-49e0-8a76-083d663f1c51
-- title:
--   Normalizing an Eisenstein-type polynomial
-- statement:
--   Let $R$ be a domain and $f\in R[X]$ monic of degree $d>0$ with constant coefficient $a\ne0$ and $a\mid f_i$ for all $i<d$. Then there is $q\in R[X]$ with
--   $$
--   f=X^d+a\,(1+Xq).
--   $$
--
--   So below the leading term $f$ is $a$ times a polynomial with constant term one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/RamifiedUnit.lean#L28-L57

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

open OAI OAI.CirculantHadamard
universe uR uS
open Polynomial
variable {R : Type uR} {S : Type uS} [CommRing R] [IsDomain R]

theorem OAI.CirculantHadamard.RamifiedUnit.exists_polynomial_unit_factor (f : R[X]) (a : R) (ha : a ≠ 0)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hzero : f.coeff 0 = a)
    (hcoeff : ∀ i < f.natDegree, a ∣ f.coeff i) :
    ∃ q : R[X], f = X ^ f.natDegree + C a * (1 + X * q) := by sorry
