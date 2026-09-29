-- Prove2me | Theorems.Thm_ModularCurve_StarBank_deltaNorm
-- name    : ModularCurve.StarBank.deltaNorm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/7b056d69-1626-5c84-9929-b988922bf6a8
-- title:
--   A norm identity for the q-expansion of Δ
-- statement:
--   Let $K$ be a field, $p$ a prime, and $\zeta \in K^\times$ a unit whose image in $K$ is a primitive $p$-th root of unity. Write $\Delta$ for the Laurent series over $K$ given by `HahnSeries.single (1 : ℤ) (1 : K)` times the $24$-th power of the image in `LaurentSeries K` of the power series `etaProd` $= \prod'_{n \ge 1}(1 - X^{n})$ with its integer coefficients mapped into $K$ along `Int.castRingHom K`; that is, $\Delta = q\prod_{n\ge1}(1-q^{n})^{24}$. For a unit $u$, `qTwist u` is the ring endomorphism of `LaurentSeries K` multiplying the coefficient of $q^{k}$ by $u^{k}$, i.e. the substitution $q \mapsto uq$, and `qExpand K N` is the ring endomorphism obtained by pushing exponents forward along multiplication by $N$ on $\mathbb{Z}$, i.e. the substitution $q \mapsto q^{N}$. The assertion is the identity in `LaurentSeries K`
--   $$\Big(\prod_{b=0}^{p-1} \Delta(\zeta^{b}q)\Big)\cdot \Delta(q^{p\cdot p}) \;=\; \Big(\prod_{b=0}^{p-1}\zeta^{b}\Big)\cdot \Delta(q^{p})^{\,p+1},$$
--   the scalar on the right being the constant Laurent series `HahnSeries.C` attached to the image in $K$ of the product of the units $\zeta^{b}$ for $b < p$ (so $1$ for odd $p$ and $-1$ for $p = 2$).
--
--   This is the formal $q$-expansion form of the classical norm relation $\prod_{b<p}\Delta((\tau+b)/p)\cdot\Delta(p\tau) = \pm\,\Delta(\tau)^{p+1}$ among the values of the discriminant form at the $p+1$ cyclic $p$-isogeny slots, here proved over an arbitrary field containing a primitive $p$-th root of unity. It is used by [`ModularCurve.StarBank.starBank`](thm.html#ModularCurve.StarBank.starBank).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_StarBank_deltaNorm.lean

import Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.StarBank.deltaNorm {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) :
    (∏ b ∈ Finset.range p, qTwist (ζ ^ b)
        (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) *
      qExpand K (p * p) (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) =
    HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) *
      qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^
        (p + 1) := by sorry
