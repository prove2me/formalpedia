-- Prove2me | Theorems.Thm_ModularCurve_restrictAlong_heckeBetaBar_frickeInvolutionBar_smul
-- name    : ModularCurve.restrictAlong_heckeBetaBar_frickeInvolutionBar_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/5873d338-2a7e-56e4-9bb9-14a15ba2cfe9
-- title:
--   Restriction along β of the Fricke translate equals restriction along α
-- statement:
--   Let $q$ be a nonzero natural number. Write $\bar F_N$ for `modularFunctionFieldBar N`, the intermediate field of $\overline{\mathbb{Q}}$-Laurent series obtained by adjoining to $\overline{\mathbb{Q}}$ the coefficientwise images of the full modular function field of level $N$ (itself $\mathbb{Q}$ adjoined to the divisor expansions of level $N$). Two $\overline{\mathbb{Q}}$-algebra maps $\bar F_1 \to \bar F_{1\cdot q}$ are in play: `heckeAlphaBar`, the inclusion coming from the containment of the level-$1$ field in the level-$q$ field, and `heckeBetaBar`, which sends a Laurent series to its $q$-fold $q$-expansion, i.e. substitutes the exponent map $n \mapsto qn$. Assume `HeckeAlphaBarIntegral` and `HeckeBetaBarIntegral`, that is, that the underlying ring homomorphisms of `heckeAlphaBar` and of `heckeBetaBar` are integral, with witnesses $h\alpha$ and $h\beta$. Let $W$ be a place of $\bar F_{1\cdot q}$ over $\overline{\mathbb{Q}}$: a valuation subring of $\bar F_{1\cdot q}$ containing the image of $\overline{\mathbb{Q}}$, distinct from the whole field, and a principal ideal ring. Then the restriction along `heckeBetaBar` of the translate of $W$ by $\overline{\mathbb{Q}}$-automorphism `frickeInvolutionBar (1 * q)` (the base change to $\overline{\mathbb{Q}}$ of the chosen Fricke automorphism of the full level-$(1\cdot q)$ field) coincides with the restriction of $W$ along `heckeAlphaBar`; here restriction along an algebra map is the pullback of the valuation subring under that map. No primality of $q$ is assumed, and the level is spelled $1 * q$.
--
--   This is the valuation-theoretic form of the identity $\pi_2 \circ w_q = \pi_1$ between the two degeneracy maps $X_0(q) \to X_0(1)$ and the Fricke involution, read on places of the geometric function fields. It is used, together with its companion for $\pi_1 \circ w_q = \pi_2$, in the analysis of prolongations of level-one places and of the cuspidal and divisor laws for pairs of places over $X_0(1)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_restrictAlong_heckeBetaBar_frickeInvolutionBar_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.restrictAlong_heckeBetaBar_frickeInvolutionBar_smul (q : ℕ) [NeZero q]
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    (frickeInvolutionBar (1 * q) • W).restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ
      = W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα := by sorry
