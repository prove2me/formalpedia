-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom
-- name    : ModularCurve.MultCovering.abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/4749a573-31bd-53b7-8087-d0e570c0e6e2
-- title:
--   Good-family values are small on supersingular annuli
-- statement:
--   Fix a prime $p$ and a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$ in the sense that $p$ is a non-unit of $A$ (`LiesOverPrime`), with residue field of characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A`, let $\Delta$ be an annulus context `AnnCtx Γ` for it, and let $\Phi$ be a good-family context `FamCtx p r` for some $r$, whose family of functions $\Phi.t =$ `goodFamily Φ` consists of elements of the field $\overline{\mathbb{Q}}(X_0(1\cdot p))$ realised as `modularFunctionFieldBar (1 * p)`. The assertion is: for every real absolute value $\mu$ on $\overline{\mathbb{Q}}$ whose closed unit ball is exactly $A$ (that is, $a \in A \iff \mu(a) \le 1$), for every index $e$ among the $\mathrm{mAnnuli}\,p = \lfloor p/12\rfloor + [p \equiv 2 \bmod 3] + [p \equiv 3 \bmod 4]$ annuli, for every place $R$ in the domain $(\Delta.\mathrm{annIn}\,e).\mathrm{dom}$ of the inner annulus $\Delta.An\,e$, and for every index $l$ with $1 \le l$, the function `goodFamily Φ l` lies in the valuation subring of $R$ — so it is regular at $R$ and its value $R.\mathrm{evalAt}$ at $R$ is defined — and that value satisfies $\mu\bigl(R.\mathrm{evalAt}(\mathrm{goodFamily}\ \Phi\ l)\bigr) < 1$, i.e. it lies in the maximal ideal of $A$. The index $l = 0$, for which the family member is $1$, is excluded.
--
--   This records the smallness of the non-constant members of the good family at all places of the supersingular annuli of the degree-$p$ covering, the strict form of integrality needed to compare values across two annuli. It is used by the cross-comparison lemmas [`ModularCurve.MultCovering.crossComparison_annIn_annIn_of_deep_of_zeroFree`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_annIn_of_deep_of_zeroFree), `…_of_eq_eleven` and `…_of_jWidth_eq_one`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ e : Fin (mAnnuli p), ∀ R ∈ (Δ.annIn e).dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
        goodFamily Φ l ∈ R.toValuationSubring ∧ μ (R.evalAt (goodFamily Φ l)) < 1 := by sorry
