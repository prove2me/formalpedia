-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_hasseExp_le_two_of_thirteen_le
-- name    : ModularCurve.MultCovering.hasseExp_le_two_of_thirteen_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/ffc79ce9-e48a-5bbf-953c-021f1e6e3a16
-- title:
--   Hasse exponents of the good family are at most two for p≥ 13
-- statement:
--   Let $p$ be a prime with $13\le p$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$, meaning that $p$ is a nonunit of $A$, whose residue field has characteristic $p$. Let $\Gamma$ be a chart context for $p$ and $A$: modular polynomial data satisfying the Kronecker congruence $\bar\Phi_p=(X^p-Y)(X-Y^p)$, integrality of the two Hecke maps $\bar\alpha,\bar\beta$ at level $1$ and $p$, a place specialisation over $A$ together with a level-one prolongation pair, a set $S_1$ of places of the level-$p$ modular function field over $\overline{\mathbb Q}$, the finset of supersingular places at level one, the finiteness of the set of supersingular $j$-invariants in the residue field together with the identification of its cardinality with $\mathrm{mAnnuli}\,p$, and a chart-supply condition. Let $\Delta$ be an annulus context over $\Gamma$: two families $\mathrm{An}_e,\mathrm{An}'_e$ of annuli over $A$ in the level-$1\cdot p$ modular function field, indexed by $e\in\mathrm{Fin}(\mathrm{mAnnuli}\,p)$, with equal domains and equal moduli, the modulus nonzero and equal to $p^{\mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e)}$ (the width being $3$, $2$ or $1$ according as the supersingular value is $0$, $1728$, or neither), the product of the two parameters equal to the image of the modulus, domain consisting exactly of the places supersingularly centred at $\mathrm{ssValue}\,\Gamma\,e$, parameter equal to $\mathrm{tieG}\,p$ whenever that value is neither $0$ nor $1728$, and the two annuli attached respectively to the source chart at the node $\mathrm{nodeSrc}\,\Gamma\,e$ and to the target chart at $\mathrm{nodeTgt}\,\Gamma\,e$. Finally let $r$ be a natural number and $\Phi$ a family context for $p$ and $r$, that is, family data whose members $t_l$ form an embedding basis of the Riemann–Roch space of the embedding divisor at level $1\cdot p$, with $t_0=1$, and satisfying the stated integrality and residue normalisations at the $\infty$-chart and at the zero-chart of every chart context over a valuation subring lying over $p$. Then for every index $l$ the natural number $\mathrm{hasseExp}$ of the underlying family data at $l$, namely the truncation to $\mathbb N$ of the integer $\mathrm{hasseContent}$, is at most $2$.
--
--   This is the uniform bound on the Hasse (Gauss) exponents of the members of the good family on the two-component covering of $X_0(p)$, obtained by playing the degree budget on the supersingular special fibre against the two-end valuation law on the supersingular annuli, and it is the point where the hypothesis $p\ge 13$ enters. It is used in the cross-comparison of annuli for the good family and in the construction of unimodular family data, in particular in the analysis of the exceptional widths at $j=0$ and $j=1728$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_hasseExp_le_two_of_thirteen_le.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.hasseExp_le_two_of_thirteen_le
    (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) : ∀ l : Fin r, hasseExp Φ.toFamData l ≤ 2 := by sorry
