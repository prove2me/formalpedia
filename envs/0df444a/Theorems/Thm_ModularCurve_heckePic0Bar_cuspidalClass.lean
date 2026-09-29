-- Prove2me | Theorems.Thm_ModularCurve_heckePic0Bar_cuspidalClass
-- name    : ModularCurve.heckePic0Bar_cuspidalClass
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/5390bfe3-91ed-5932-9c5e-3584bf40d8d1
-- title:
--   Hecke correspondence scales the cuspidal class by 1+ℓ
-- statement:
--   Let $N$ and $\ell$ be nonzero natural numbers, and work over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Let $\bar F_N$ denote `modularFunctionFieldBar N`, the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N$ inside $\overline{\mathbb{Q}}((q))$-type Laurent series, and likewise $\bar F_{N\ell}$ at level $N\ell$. The two degeneracy legs are `heckeAlphaBar`, the inclusion $\bar F_N \hookrightarrow \bar F_{N\ell}$ coming from the containment of function fields, and `heckeBetaBar`, the map $\bar F_N \to \bar F_{N\ell}$ induced by $q \mapsto q^{\ell}$ on $q$-expansions and the identity on $\overline{\mathbb{Q}}$. The hypotheses are: $h\alpha$ and $h\beta$, integrality of the ring homomorphisms underlying `heckeAlphaBar` and `heckeBetaBar`; the assumption `HasPrincipalDivisors` for $\bar F_{N\ell}$, that every nonzero function has a degree-zero divisor recording its order at each place; $hFI$, the fundamental identity for the extension $\bar F_N \subseteq \bar F_{N\ell}$ along $\beta$; $hfin$, module-finiteness of $\bar F_{N\ell}$ over $\bar F_N$ along $\alpha$; $hN$, the pushforward norm formula for divisors along $\alpha$; and $hdiv$, the divisor-level relation that the correspondence `heckeDivBar` (pullback along $\beta$ followed by pushforward along $\alpha$) sends the cuspidal divisor $(\bar 0) - (\bar\infty)$ of level $N$ to $(1+\ell)$ times itself. The conclusion is that the induced endomorphism `heckePic0Bar` of $\mathrm{Pic}^0(\bar F_N)$ sends the cuspidal class `cuspidalClass N`, the class of the degree-zero divisor $(\bar 0) - (\bar\infty)$, to $(1+\ell)$ times that class.
--
--   This is the eigenvalue relation $T_\ell c = (1+\ell)c$ for the cuspidal class $c = [(0) - (\infty)]$ on the Jacobian $J_0(N)$, here in the conditional form in which the divisor-level relation is taken as a hypothesis. It is used downstream for the action of the Hecke operators on the cuspidal class and for the statement that the Eisenstein ideal annihilates it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckePic0Bar_cuspidalClass.lean

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.heckePic0Bar_cuspidalClass (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ) [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))] (hFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ) (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)) (hN : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hfin) (hdiv : heckeDivBar hα hβ (cuspidalDivisor N) = (1 + ℓ : ℤ) • cuspidalDivisor N) : heckePic0Bar hα hβ hFI hfin hN (cuspidalClass N) = (1 + ℓ : ℤ) • cuspidalClass N := by sorry
