-- Prove2me | Theorems.Thm_ModularCurve_thetaL_qExpand
-- name    : ModularCurve.thetaL_qExpand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/26c5c7a3-c7b5-5b02-9bd6-2300870ec02b
-- title:
--   q d/dq commutes with q ↦ q^N up to N
-- statement:
--   Let $K$ be a field, let $N$ be a natural number that is nonzero, and let $x$ be a formal Laurent series over $K$ (an element of `LaurentSeries K`, i.e. a Hahn series over $K$ with value group $\mathbb{Z}$). Two operations on `LaurentSeries K` are involved. First, [`ModularCurve.thetaL K`](def/ModularCurve_QExpansionDiff.html#L16) is the $K$-linear endomorphism sending $f$ to $\mathrm{single}(1,1)\cdot f'$, where $f'$ is the formal derivative of $f$ and $\mathrm{single}(1,1)$ is the monomial $q$; thus it is the derivation $\theta = q\,d/dq$. Second, [`ModularCurve.qExpand K N`](def/ModularCurve_X0.html#L25) is the ring homomorphism obtained by pushing the exponent support forward along the (strictly monotone, injective) map $n \mapsto Nn$ on $\mathbb{Z}$, that is, the substitution $q \mapsto q^{N}$ on Laurent series. The assertion is the identity $$\theta\bigl(x(q^{N})\bigr) = \mathrm{single}(0,N)\cdot (\theta x)(q^{N}),$$ where $\mathrm{single}(0,N)$ is the constant Laurent series with value the image of $N$ in $K$; equivalently, applying $\theta$ after the substitution $q \mapsto q^N$ equals $N$ times the substitution applied after $\theta$.
--
--   This is the chain rule for the substitution $q \mapsto q^{N}$ with respect to the derivation $q\,d/dq$ on the field of formal Laurent series. It is used whenever $q$-expansions at different levels are compared after applying $\theta$, for instance in the computations with Hecke multipliers, Fricke involutions and $j$-expansions that occur in the treatment of the modular curves $X_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_thetaL_qExpand.lean

import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.thetaL_qExpand (K : Type*) [Field K] (N : ℕ) [NeZero N] (x : LaurentSeries K) :
    ModularCurve.thetaL K (ModularCurve.qExpand K N x) =
      HahnSeries.single (0 : ℤ) (N : K) * ModularCurve.qExpand K N (ModularCurve.thetaL K x) := by sorry
