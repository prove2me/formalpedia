-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_evalAt_goodFamily_mem_maximalIdeal_of_mem_annIn_dom
-- name    : ModularCurve.MultCovering.evalAt_goodFamily_mem_maximalIdeal_of_mem_annIn_dom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/22109543-2c87-5ec2-a966-ea97e7f03c69
-- title:
--   Good-family values lie in mathfrak m_A on the inner annuli
-- statement:
--   Fix a prime $p$ (as a natural number with a primality instance) and a valuation subring $A$ of $\overline{\mathbb Q}=$ `AlgebraicClosure ℚ` such that `A.LiesOverPrime p`, i.e. the image of $p$ in $\overline{\mathbb Q}$ is a non-unit of $A$; the residue field of $A$ carries decidable equality and characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A` for level $1\cdot p$, let $\Delta$ be an annulus context `AnnCtx Γ`, and let $\Phi$ be a family context `FamCtx p r` for some $r$, whose underlying tuple of modular functions is $t=$ `goodFamily Φ` $: \mathrm{Fin}\,r \to$ `modularFunctionFieldBar (1 * p)`. The assertion is: for every index $e$ of the $\mathrm{mAnnuli}\,p = \lfloor p/12\rfloor + [p\equiv 2 \bmod 3] + [p \equiv 3 \bmod 4]$ annuli, every place $R$ of `modularFunctionFieldBar (1 * p)` over $\overline{\mathbb Q}$ belonging to the domain `(Δ.annIn e).dom` of the inner annulus $\Delta.\mathrm{An}\,e$, and every index $l$ with $1\le l$, the function $t_l$ lies in the valuation subring of $R$ (so it is regular at $R$), and its value $R.\mathrm{evalAt}(t_l) \in \overline{\mathbb Q}$ lies in $A$ and, viewed as an element of $A$, lies in the maximal ideal of $A$.
--
--   This is the absolute-value-free form of the smallness statement for the members $t_l$, $l\ge 1$, of the good family at the places of the supersingular annuli of the prime-level covering: their values are topologically small, i.e. lie in $\mathfrak m_A$. It is used in the construction of a uniform multiplicative covering with a certified family, [`ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_evalAt_goodFamily_mem_maximalIdeal_of_mem_annIn_dom.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.MultCovering

theorem ModularCurve.MultCovering.evalAt_goodFamily_mem_maximalIdeal_of_mem_annIn_dom (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) :
    ∀ e : Fin (mAnnuli p), ∀ R ∈ (Δ.annIn e).dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
      goodFamily Φ l ∈ R.toValuationSubring ∧
      ∃ h : R.evalAt (goodFamily Φ l) ∈ A, (⟨_, h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by sorry
