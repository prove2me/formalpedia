-- Prove2me | Theorems.Thm_HahnSeries_hasRamBound_one_of_forall_ringEquiv_apply_eq
-- name    : HahnSeries.hasRamBound_one_of_forall_ringEquiv_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/4b526abf-db34-59d8-87de-575bb8c429d0
-- title:
--   Descent to integer exponents in the Hahn field K((t^ℚ))
-- statement:
--   Let $K$ be a field that is algebraically closed and of characteristic zero, and consider the Hahn series field $\mathrm{HahnSeries}\ \mathbb Q\ K$, whose elements are formal series with coefficients in $K$ supported on a well-ordered set of rational exponents. For $e : \mathbb N$ and a Hahn series $y$, the predicate [`HahnSeries.HasRamBound e y`](def/HahnSeries_RamificationBound.html#L32) asserts that the support of $y$ is contained in the set of rationals of the form $k/e$ with $k \in \mathbb Z$; thus [`HahnSeries.HasRamBound 1 y`](def/HahnSeries_RamificationBound.html#L32) says exactly that every exponent occurring in $y$ is an integer, i.e. that $y$ lies in the Laurent subfield $K((t)) \subseteq K((t^{\mathbb Q}))$. Let $x$ be a Hahn series with rational exponents over $K$, and assume that for every ring isomorphism $\sigma$ of $\mathrm{HahnSeries}\ \mathbb Q\ K$ onto itself which preserves `orderTop`, in the sense that $(\sigma z).\mathrm{orderTop} = z.\mathrm{orderTop}$ for all $z$, and which fixes every series all of whose exponents are integers, one has $\sigma x = x$. The conclusion is that the support of $x$ consists of integers, i.e. [`HahnSeries.HasRamBound 1 x`](def/HahnSeries_RamificationBound.html#L32) holds.
--
--   This is the elementwise form of the descent statement that the fixed field of the `orderTop`-preserving automorphisms of $K((t^{\mathbb Q}))$ fixing $K((t))$ pointwise is $K((t))$ itself, the Galois-theoretic half of the Puiseux tower $K((t)) \subset K((t^{1/e})) \subset K((t^{\mathbb Q}))$; note that the automorphisms quantified over are merely ring isomorphisms, not assumed $K$-linear. It is used to bound ramification of Puiseux expansions attached to torsion points of a Weierstrass curve over a power series ring, in [`WeierstrassCurve.hasRamBound_one_of_nsmul_eq_zero_of_isUnit_discriminant_powerSeries`](thm.html#WeierstrassCurve.hasRamBound_one_of_nsmul_eq_zero_of_isUnit_discriminant_powerSeries).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HahnSeries_hasRamBound_one_of_forall_ringEquiv_apply_eq.lean

import Mathlib
import Definitions.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HahnSeries.hasRamBound_one_of_forall_ringEquiv_apply_eq
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {x : HahnSeries ℚ K}
    (hx : ∀ σ : HahnSeries ℚ K ≃+* HahnSeries ℚ K,
      (∀ z : HahnSeries ℚ K, (σ z).orderTop = z.orderTop) →
      (∀ z : HahnSeries ℚ K, HahnSeries.HasRamBound 1 z → σ z = z) → σ x = x) :
    HahnSeries.HasRamBound 1 x := by sorry
