-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_eq_eleven
-- name    : ModularCurve.MultCovering.crossComparison_annIn_annIn_of_eq_eleven
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/fdaca332-642d-53d0-a0ca-5d8280e546df
-- title:
--   Cross-tube chordal comparison for X₀(11)
-- statement:
--   Let $p$ be a prime with $p = 11$ (so that $\mathrm{mAnnuli}\,p = p/12 + [p \equiv 2 \bmod 3] + [p \equiv 3 \bmod 4] = 2$), let $r$ be a natural number and let $\Phi$ be a family context `FamCtx p r`: family data whose $r$ members form an embedding basis at level $1\cdot p$, are normalised to $1$ at index $0$, and satisfy the prescribed integrality and residue conditions at the infinite and zero charts (these conditions are summarised here). Let $s : \mathrm{Fin}\,r \to \overline{\mathbb{Q}}\text{-modular function field}$ at level $1\cdot p$ satisfy `IsEmbBasis`, i.e. $s$ is linearly independent over $\overline{\mathbb{Q}}$ and its span is the Riemann–Roch space of the embedding divisor at that level. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ is a non-unit of $A$, with decidable equality and characteristic $p$ on its residue field, let $\Gamma$ be a chart context for $p$ and $A$, let $\Delta$ be an annulus context over $\Gamma$, and let $e \neq e'$ be indices in $\mathrm{Fin}(\mathrm{mAnnuli}\,p)$. Then for every non-archimedean real absolute value $\mu$ on $\overline{\mathbb{Q}}$ whose unit ball is exactly $A$ (that is, $a \in A \iff \mu(a) \le 1$), for every place $R$ in the domain of the annulus $\Delta.\mathrm{annIn}\,e = \Delta.\mathrm{An}\,e$ and every place $R'$ in the domain of $\Delta.\mathrm{annIn}\,e'$, if the evaluation vectors $x = \mathrm{evalVec}\,s\,R$ and $y = \mathrm{evalVec}\,s\,R'$ (whose $i$-th entries are the values at $R$, resp. $R'$, of $s_i$ divided by $s$ at the pivot index) are non-proportional, in the sense that $x_{i'}y_{j'} \neq x_{j'}y_{i'}$ for some $i', j'$, then $$\bigl|\log(\textstyle\sup_i \mu(x_i)) + \log(\sup_j \mu(y_j)) - \log(\sup_{(i,j)} \mu(x_i y_j - x_j y_i))\bigr| \le 4\bigl(\mathrm{linkBudget}(\Phi, s, hs) + \mathrm{modulusExp}\bigr)\cdot(-\log \mu(p)),$$ the left-hand side being $|\mathrm{prox}_\mu(x,y)|$ and the right-hand factor $\mathrm{compConst}(\Phi, s, hs)$.
--
--   This is the cross-tube case of the chordal comparison estimate on the multiplicative covering of $X_0(p)$, for two distinct supersingular annuli (at $p = 11$ these correspond to the supersingular invariants $j = 0$ and $j = 1728$, of widths $3$ and $2$). It is the $p = 11$ instance of the general statement [`ModularCurve.MultCovering.crossComparison_annIn_annIn`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_annIn), which cites it alongside the cases handled by the generic deep/outer arguments available for larger primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_eq_eleven.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.MultCovering

theorem ModularCurve.MultCovering.crossComparison_annIn_annIn_of_eq_eleven (p : ℕ) [Fact p.Prime] (hp11 : p = 11) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (e e' : Fin (mAnnuli p)) (hne : e ≠ e') :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ R ∈ (Δ.annIn e).dom, ∀ R' ∈ (Δ.annIn e').dom,
        (∃ i' j', evalVec s R i' * evalVec s R' j' ≠ evalVec s R j' * evalVec s R' i') →
        |prox μ (evalVec s R) (evalVec s R')| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by sorry
