-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_weightTwo_coeff_sum_slots
-- name    : ModularCurve.PhiGen.weightTwo_coeff_sum_slots
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/b34ceb31-de5a-5755-9d3b-5db3ed6e164e
-- title:
--   Coefficient at ℓ n of ℓ² f(q^{ℓ^2})+sum_b f(ζᵇ q)
-- statement:
--   Let $K$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $\ell$ be a nonzero natural number, and let $\zeta \in K^\times$ be a unit whose underlying element $(\zeta : K)$ is a primitive $\ell$-th root of unity. Let $f$ be a Laurent series over $K$ and let $n$ be an integer. Two operations on $K((q))$ occur. First, `qExpand K (ℓ * ℓ)` is the ring homomorphism obtained by embedding the index domain along multiplication by $\ell^2$ on $\mathbb{Z}$; it sends $f$ to the series whose coefficient at $\ell^2 k$ is the coefficient of $f$ at $k$ and whose coefficients at indices not divisible by $\ell^2$ vanish, i.e. to $f(q^{\ell^2})$. Second, for a unit $u$, `qTwist u` is the ring homomorphism whose value at $f$ has coefficient $u^k \cdot a_k(f)$ in degree $k$, i.e. $f(uq)$. The assertion is that the series $\ell^2 \cdot f(q^{\ell^2}) + \sum_{b \in \{0,\dots,\ell-1\}} f(\zeta^b q)$, where the first term is the natural-number scalar multiple by $\ell \cdot \ell$, has coefficient in degree $\ell n$ equal to $\ell \bigl(a_{\ell n}(f) + \ell\, a_{n/\ell}(f)\bigr)$ if $\ell \mid n$ in $\mathbb{Z}$, and equal to $\ell\, a_{\ell n}(f)$ otherwise, the division $n/\ell$ being integer division.
--
--   This is the formal $q$-expansion form of the weight-two slot-sum identity: the coefficients of the combination $\ell^2 f(q^{\ell^2}) + \sum_{b<\ell} f(\zeta^b q)$ in degrees divisible by $\ell$ carry exactly the $\ell$-weights appearing in the weight-two Hecke formula, here as a purely formal statement about Laurent series and not about differentials or divisors. It is obtained from the root-of-unity annihilation identity [`ModularCurve.PhiGen.sum_qTwist_coeff`](thm.html#ModularCurve.PhiGen.sum_qTwist_coeff), and is used by [`ModularCurve.qExpansionDiff_traceDiff_pullbackDiff_smul_D`](thm.html#ModularCurve.qExpansionDiff_traceDiff_pullbackDiff_smul_D).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_weightTwo_coeff_sum_slots.lean

import Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.weightTwo_coeff_sum_slots {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [NeZero ℓ] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (f : LaurentSeries K) (n : ℤ) : ((ℓ * ℓ) • qExpand K (ℓ * ℓ) f + ∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) f).coeff ((ℓ : ℤ) * n) = (ℓ : K) * (f.coeff ((ℓ : ℤ) * n) + if (ℓ : ℤ) ∣ n then (ℓ : K) * f.coeff (n / ℓ) else 0) := by sorry
