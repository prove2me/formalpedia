-- Prove2me | Theorems.Thm_LocalGL2_localHeckeMul_comm
-- name    : LocalGL2.localHeckeMul_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/228d6d7f-bc8f-5d25-9e25-9875ab71a2cd
-- title:
--   Commutativity of the local spherical Hecke algebra of GL₂
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with the `IsDiscreteValuationRing` property), let $K$ be a field equipped with an $R$-algebra structure making it a fraction field of $R$, and let $R_0$ be an arbitrary commutative coefficient ring. Write $U =$ `integralSubgroup R K` for the subgroup of $\mathrm{GL}_2(K)$ given by the range of the group homomorphism $\mathrm{GL}_2(R) \to \mathrm{GL}_2(K)$ obtained by applying `algebraMap R K` entrywise, i.e. the subgroup of invertible $2\times 2$ matrices over $K$ that arise from invertible matrices over $R$. The Hecke algebra [`HeckePair.HeckeAlgebra U R₀`](def/LocalLanglands_HeckePair.html#L63) is the $R_0$-submodule of the functions $\mathrm{GL}_2(K) \to R_0$ cut out by the predicate `IsHeckeFun` relative to $U$ (the closure of this condition under addition, zero and scalar multiplication being what makes it a submodule), carrying a multiplication given by convolution. The theorem asserts that for all elements $f_1, f_2$ of this algebra one has $f_1 \cdot f_2 = f_2 \cdot f_1$; that is, the local Hecke algebra attached to the pair $(\mathrm{GL}_2(K), \mathrm{GL}_2(R))$ with coefficients in $R_0$ is commutative.
--
--   This is the classical commutativity of the spherical (unramified) local Hecke algebra of $\mathrm{GL}_2$ over a discretely valued field, the statement that allows one to speak of characters of the local Hecke algebra and hence underlies the Satake parametrisation at unramified places. It is used in the treatment of automorphic forms, in the decomposition of cuspidal constituents under finitely many Hecke operators and in the construction of a Hecke algebra homomorphism matching local data at inert primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_localHeckeMul_comm.lean

import Mathlib
import Definitions.Def_LocalLanglands_CartanDecomposition
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_LocalLanglands_GelfandInvolution
import Definitions.Def_LocalLanglands_LocalHeckeInstance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Matrix LocalGL2 HeckePair

theorem LocalGL2.localHeckeMul_comm
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {R₀ : Type*} [CommRing R₀]
    (f₁ f₂ : HeckePair.HeckeAlgebra (integralSubgroup R K) R₀) :
    f₁ * f₂ = f₂ * f₁ := by sorry
