-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_sum_qTwist_coeff
-- name    : ModularCurve.PhiGen.sum_qTwist_coeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/a671034f-d53b-5757-9df2-3d57dbe05eeb
-- title:
--   Summing q-twists over the ℓ-th roots of unity
-- statement:
--   Let $K$ be a field carrying a $\mathbb{Q}$-algebra structure, let $\ell$ be a natural number, and let $\zeta$ be a unit of $K$ whose underlying element is a primitive $\ell$-th root of unity. For a unit $u$ of a commutative ring, `qTwist u` denotes the ring endomorphism of the Laurent series (Hahn series over $\mathbb{Z}$) that multiplies the coefficient of index $k \in \mathbb{Z}$ by the integral power $u^{k}$, i.e. formally the substitution $f(q) \mapsto f(uq)$. The assertion is that for every Laurent series $f$ over $K$ and every integer $k$, the $k$-th coefficient of $\sum_{b=0}^{\ell-1} \mathrm{qTwist}(\zeta^{b})\,f$ equals $\ell \cdot a_k(f)$, where $a_k(f)$ is the $k$-th coefficient of $f$ and $\ell$ is read in $K$, when $\ell$ divides $k$ in $\mathbb{Z}$, and equals $0$ otherwise. No restriction is placed on $\ell$: for $\ell = 0$ the sum is empty and both sides vanish, and for $\ell = 1$ the statement is trivial.
--
--   This is the orthogonality relation for the $\ell$-th roots of unity, in the form in which it is applied to formal $q$-expansions: averaging a Laurent series over the twists $q \mapsto \zeta^{b} q$ projects onto the coefficients in degrees divisible by $\ell$. It is used in the coefficient computations for the $q$-expansion model of the modular curve, notably by [`ModularCurve.PhiGen.weightTwo_coeff_sum_slots`](thm.html#ModularCurve.PhiGen.weightTwo_coeff_sum_slots), [`ModularCurve.theta_coeff`](thm.html#ModularCurve.theta_coeff) and [`ModularCurve.theta_mul`](thm.html#ModularCurve.theta_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_sum_qTwist_coeff.lean

import Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.sum_qTwist_coeff {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (f : LaurentSeries K) (k : ℤ) : (∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) f).coeff k = if (ℓ : ℤ) ∣ k then (ℓ : K) * f.coeff k else 0 := by sorry
