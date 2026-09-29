-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_hasseExp_zero
-- name    : ModularCurve.MultCovering.hasseExp_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/7dcd9746-8590-5ff4-8206-324fac376768
-- title:
--   The Hasse exponent vanishes at index zero
-- statement:
--   Let $p$ be a prime and $r$ a natural number, and let $\Phi$ be a family context `FamCtx p r` for $p$: that is, a family $t : \mathrm{Fin}\,r \to \overline{\mathbb{Q}}$-modular functions in `modularFunctionFieldBar (1 * p)`, each obtained by coefficientwise embedding from a function $tRat\,l$ in `modularFunctionFieldFull (1 * p)`, subject to the further conditions packaged in `FamCtx`: the $t\,l$ are linearly independent over $\overline{\mathbb{Q}}$ and span the Riemann–Roch space of `embDivisor (1 * p)` (`IsEmbBasis`); $t\,l = 1$ whenever $l = 0$; and two conditions, `t_inf` and `t_zeroChart`, describing for every valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $p$ and every chart context $\Gamma$ on $A$ the residues of the $t\,l$ in the chart at infinity, respectively the residues of the normalised members `goodFamilyZero`, as the supersingular polynomial times a basis of polynomials in $\bar j$ of bounded degree (these hypotheses are summarised here). The assertion is that for every index $l \in \mathrm{Fin}\,r$ with $(l : \mathbb{N}) = 0$ one has $\mathrm{hasseExp}\,\Phi.\mathrm{toFamData}\,l = 0$, i.e. the natural number obtained by truncating the $p$-adic content $\mathrm{hasseContent}$ — the least $p$-adic valuation of a nonzero coefficient of the Laurent series `zeroSeries Φ l`, when such a least value exists, and $0$ otherwise — is zero.
--
--   This records the normalisation of the exponent vector $(n_l)$ attached to a good family at its constant member $t_0 = 1$, whose $q$-expansion at the zero cusp has trivial $p$-adic content. It is used in the comparison of the annuli of the multiplicative covering across the two charts and in the construction of family contexts from bifiltered data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_hasseExp_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.hasseExp_zero {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r) :
    ∀ l : Fin r, (l : ℕ) = 0 → hasseExp Φ.toFamData l = 0 := by sorry
