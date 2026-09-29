-- Prove2me | Theorems.Thm_ModularCurve_heckeDivBar_cuspidalDivisor
-- name    : ModularCurve.heckeDivBar_cuspidalDivisor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/c5f57ee6-0301-5857-bc43-946b5c05843e
-- title:
--   Hecke correspondence acts on the cuspidal divisor by 1+ℓ
-- statement:
--   Let $N$ and $\ell$ be nonzero natural numbers and work over $\overline{\mathbb{Q}}$ with the base-changed modular function fields $\mathtt{modularFunctionFieldBar}\,N$ and $\mathtt{modularFunctionFieldBar}\,(N\ell)$, together with the two degeneracy $\overline{\mathbb{Q}}$-algebra maps $\alpha=\mathtt{heckeAlphaBar}$ (inclusion of levels) and $\beta=\mathtt{heckeBetaBar}$ ($q$-expansion twist) from level $N$ to level $N\ell$; assume both are integral as ring maps (the hypotheses $h\alpha$, $h\beta$) and that every nonzero element of the level-$N\ell$ field has a principal divisor of degree $0$. Let $W_1 \neq W_2$ be places of the level-$N\ell$ field such that the $\beta$-fibre over the cusp $\mathtt{cuspInftyBar}\,N$ consists exactly of $W_1$ and $W_2$, with ramification indices along $\beta$ equal to $1$ and $\ell$ respectively, each restricting along $\alpha$ to $\mathtt{cuspInftyBar}\,N$ with inertia degree along $\alpha$ equal to $1$. Let $V_1 \neq V_2$ satisfy the same conditions over $\mathtt{cuspZeroBar}\,N$ (the Fricke translate of $\mathtt{cuspInftyBar}\,N$), with ramification indices $\ell$ and $1$ along $\beta$, restrictions along $\alpha$ equal to $\mathtt{cuspZeroBar}\,N$ and inertia degrees $1$. Then the divisor correspondence $\mathtt{heckeDivBar}$ built from $\beta$ and $\alpha$ sends the cuspidal divisor $(\mathtt{cuspZeroBar}\,N) - (\mathtt{cuspInftyBar}\,N)$ to $(1+\ell)$ times itself.
--
--   This is the divisor-level Hecke relation $T_\ell\bigl((0)-(\infty)\bigr) = (1+\ell)\bigl((0)-(\infty)\bigr)$ on the modular curve of level $N$ over $\overline{\mathbb{Q}}$, here in conditional form: the two-cusp fibre data for the pair of degeneracy maps $X_0(N\ell) \rightrightarrows X_0(N)$ are hypotheses rather than conclusions. It feeds the prime-level version [`ModularCurve.heckeDivBar_cuspidalDivisor_of_prime`](thm.html#ModularCurve.heckeDivBar_cuspidalDivisor_of_prime), and thence the computation of the order of the cuspidal divisor class. Neither primality of $\ell$ nor any further arithmetic of the level enters the computation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeDivBar_cuspidalDivisor.lean

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.heckeDivBar_cuspidalDivisor (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ) [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))] (W₁ W₂ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))) (hW : W₁ ≠ W₂) (hfibInf : ∀ W, W ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ (cuspInftyBar N) ↔ W = W₁ ∨ W = W₂) (heβW₁ : Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) W₁ = 1) (heβW₂ : Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) W₂ = ℓ) (hrαW₁ : W₁.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα = cuspInftyBar N) (hrαW₂ : W₂.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα = cuspInftyBar N) (hfαW₁ : Place.inertiaDegAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα W₁ = 1) (hfαW₂ : Place.inertiaDegAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα W₂ = 1) (V₁ V₂ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))) (hV : V₁ ≠ V₂) (hfibZero : ∀ V, V ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ (cuspZeroBar N) ↔ V = V₁ ∨ V = V₂) (heβV₁ : Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) V₁ = ℓ) (heβV₂ : Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) V₂ = 1) (hrαV₁ : V₁.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα = cuspZeroBar N) (hrαV₂ : V₂.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα = cuspZeroBar N) (hfαV₁ : Place.inertiaDegAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα V₁ = 1) (hfαV₂ : Place.inertiaDegAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα V₂ = 1) : heckeDivBar hα hβ (cuspidalDivisor N) = (1 + ℓ : ℤ) • cuspidalDivisor N := by sorry
