-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_AnnCtx_exists_mem_dom_abv_evalAt_param_ne
-- name    : ModularCurve.MultCovering.AnnCtx.exists_mem_dom_abv_evalAt_param_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/43d63662-57e3-5456-a99c-b7b71491eb0a
-- title:
--   Annuli of the multiplicative covering are not circles
-- statement:
--   Let $p$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field has characteristic $p$, let $\Gamma$ be a chart context `ChartCtx p A` for the prime level $p$ multiplicative covering, and let $\Delta$ be an annulus context `AnnCtx Γ`, so that for each index $e$ in `Fin (mAnnuli p)` (where $\mathrm{mAnnuli}\,p = \lfloor p/12\rfloor + [p\equiv 2 \bmod 3] + [p\equiv 3 \bmod 4]$) the datum $\Delta.\mathrm{annIn}\,e = \Delta.\mathrm{An}\,e$ is an annulus in the function field $\overline{\mathbb Q}(X_0(p))$, i.e. `modularFunctionFieldBar (1 * p)`: a set $\mathrm{dom}$ of places of that field over $\overline{\mathbb Q}$, a parameter $z \in \overline{\mathbb Q}(X_0(p))$, and a modulus in the maximal ideal of $A$, equal by the context to $p^{\mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e)}$ and nonzero in $\overline{\mathbb Q}$, subject to the annulus axioms, among them: every admissible constant $c$ (an element of $\mathfrak m_A$, nonzero, with $\mathrm{modulus} = c\,m$ for some $m \in \mathfrak m_A$) is the value $P.\mathrm{evalAt}\,z$ of the parameter at a unique place $P$ of $\mathrm{dom}$, where $\mathrm{evalAt}$ denotes the residue of an integral element pulled back to $\overline{\mathbb Q}$ along the inverse of the structure map into the residue field (and $0$ for non-integral elements). Fix such an index $e$ and an absolute value $\mu \colon \overline{\mathbb Q} \to \mathbb R$ whose unit ball is exactly $A$, that is, $a \in A \iff \mu(a) \le 1$ for all $a$. Then there are places $Q_1, Q_2$ in the domain of $\Delta.\mathrm{annIn}\,e$ with $\mu(Q_1.\mathrm{evalAt}\,z) \ne \mu(Q_2.\mathrm{evalAt}\,z)$.
--
--   This is the wideness statement for the supersingular annuli of the multiplicative covering: the parameter does not have constant absolute value on the annulus domain, so the annulus is not a single circle. It is used in the comparison of absolute values of parameters and good families along the supersingular tube, for instance in [`ModularCurve.MultCovering.abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom`](thm.html#ModularCurve.MultCovering.abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom) and in the cross-comparison of inner annuli.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_AnnCtx_exists_mem_dom_abv_evalAt_param_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.AnnCtx.exists_mem_dom_abv_evalAt_param_ne
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    {Γ : ChartCtx p A} (Δ : AnnCtx Γ) (e : Fin (mAnnuli p))
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    ∃ Q₁ ∈ (Δ.annIn e).dom, ∃ Q₂ ∈ (Δ.annIn e).dom,
      μ (Q₁.evalAt (Δ.annIn e).param) ≠ μ (Q₂.evalAt (Δ.annIn e).param) := by sorry
