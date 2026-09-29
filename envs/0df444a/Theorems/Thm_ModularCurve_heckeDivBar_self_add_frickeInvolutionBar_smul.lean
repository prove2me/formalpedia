-- Prove2me | Theorems.Thm_ModularCurve_heckeDivBar_self_add_frickeInvolutionBar_smul
-- name    : ModularCurve.heckeDivBar_self_add_frickeInvolutionBar_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/d76a2301-d47b-5f91-9951-5cdcf2508121
-- title:
--   Fibre identification Uₚ D + wₚ· D = σ^*ι_* D on X₀(p)
-- statement:
--   Let $p$ be a prime, and work over $\overline{\mathbb{Q}}$, taken as `AlgebraicClosure ℚ`, with the function fields `modularFunctionFieldBar N` obtained by base change of the level-$N$ modular function field to $\overline{\mathbb{Q}}$. Assume: the ring homomorphisms underlying the two level-raising maps `heckeAlphaBar` and `heckeBetaBar` from level $p$ to level $p\cdot p$ are integral (the predicates `HeckeAlphaBarIntegral` and `HeckeBetaBarIntegral` at $N=\ell=p$); every nonzero element of `modularFunctionFieldBar (p * p)` and of `modularFunctionFieldBar p` has a degree-zero divisor whose coefficient at each place $v$ is $v.\mathrm{ord}$ of that element; and the two $\overline{\mathbb{Q}}$-algebra maps from level $1$ to level $p$ are integral, namely the inclusion `towerInclBar` and the map `towerSubstBar`, which is `heckeBetaBar` at $N=1,\ \ell=p$ followed by that inclusion. Then for every divisor $D$ on `modularFunctionFieldBar p`, that is, every finitely supported $\mathbb{Z}$-valued function on its places, the sum of $D$ pulled back along `heckeBetaBar` and pushed forward along `heckeAlphaBar` (the correspondence `heckeDivBar`) and of the transport of $D$ by the Fricke automorphism `frickeInvolutionBar p` equals the pullback along `towerSubstBar` of the pushforward of $D$ along `towerInclBar`.
--
--   This is the $(p,p)$ fibre identification on $X_0(p)$: the fibre product $X_0(p)\times_{X_0(1)}X_0(p)$ decomposes into $X_0(p^2)$ together with the graph of the Fricke involution, the double cosets of $\Gamma_0(p)$ in $\mathrm{SL}_2(\mathbb{Z})$ being represented by $1$ and $w_p$, and the identity is asserted here exactly at the level of divisors. It is the geometric input to [`ModularCurve.heckeOperatorBar_self_add_frickeInvolutionBar_smul`](thm.html#ModularCurve.heckeOperatorBar_self_add_frickeInvolutionBar_smul), where the right-hand side factors through the trivial degree-zero class group of level $1$ and yields $U_p=-w_p$ on $J_0(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeDivBar_self_add_frickeInvolutionBar_smul.lean

import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.heckeDivBar_self_add_frickeInvolutionBar_smul (p : ℕ) [Fact p.Prime]
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) p p)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) p p)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * p))]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar p)]
    (hι : (towerInclBar (AlgebraicClosure ℚ) (one_dvd p)).toRingHom.IsIntegral)
    (hσ : (towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd)).toRingHom.IsIntegral)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) :
    heckeDivBar hα hβ D + frickeInvolutionBar p • D =
      Divisor.pullbackAlong (towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd)) hσ
        (Divisor.pushforwardAlong (towerInclBar (AlgebraicClosure ℚ) (one_dvd p)) hι D) := by sorry
