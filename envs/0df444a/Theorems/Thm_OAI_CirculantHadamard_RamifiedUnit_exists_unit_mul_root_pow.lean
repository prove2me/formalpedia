-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_RamifiedUnit_exists_unit_mul_root_pow
-- name    : OAI.CirculantHadamard.RamifiedUnit.exists_unit_mul_root_pow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:22:55.895991+00:00
-- url     : https://prove2.me/theorems/ebab4217-a1e7-4af2-aeef-3c3e65555724
-- title:
--   The constant term is a unit times a power of a root in the maximal ideal
-- statement:
--   Let $R$ be a domain, $S$ a local $R$-algebra, and $f\in R[X]$ monic of degree $d>0$ with constant coefficient $a\ne0$ and $a\mid f_i$ for $i<d$. If $z$ lies in the maximal ideal of $S$ and $f(z)=0$, then there is a unit $w$ of $S$ with
--   $$
--   a=w\,z^{d}\quad\text{in }S .
--   $$
--
--   This is the standard fact that the constant term of an Eisenstein polynomial is a unit multiple of the $d$th power of a root.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/RamifiedUnit.lean#L61-L87

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
variable [CommRing S] [Algebra R S] [IsLocalRing S]

theorem OAI.CirculantHadamard.RamifiedUnit.exists_unit_mul_root_pow (f : R[X]) (a : R) (ha : a ≠ 0)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hzero : f.coeff 0 = a)
    (hcoeff : ∀ i < f.natDegree, a ∣ f.coeff i)
    (z : S) (hz : z ∈ IsLocalRing.maximalIdeal S) (hroot : aeval z f = 0) :
    ∃ u : Sˣ, algebraMap R S a = (u : S) * z ^ f.natDegree := by sorry
