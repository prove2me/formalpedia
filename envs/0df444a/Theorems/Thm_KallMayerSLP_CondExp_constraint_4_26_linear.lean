-- Prove2me | Theorems.Thm_KallMayerSLP_CondExp_constraint_4_26_linear
-- name    : KallMayerSLP.CondExp.constraint_4_26_linear
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:25.706868+00:00
-- url     : https://prove2.me/theorems/2ba95505-1b56-44f2-bd69-8da9dfbd138f
-- title:
--   §4.2, p.159 — constraint (4.26) is the deterministic linear constraint $t^{\mathrm T}x\ge l^{-1}(\gamma)$
-- statement:
--   Let $\xi$ be a random variable with a log-concave density and finite expectation, let $l$ be its mean residual life, and let $\zeta(x,\xi)=t^{\mathrm T}x-\xi$ with a deterministic vector $t\in\mathbb R^n$. For every $x\in\mathbb R^n$,
--   $$
--   \mathbb E_\xi[-\zeta(x,\xi)\mid\zeta(x,\xi)<0]=l(t^{\mathrm T}x),
--   $$
--   and for every real $\gamma$,
--   $$
--   l(t^{\mathrm T}x)\le\gamma\iff t^{\mathrm T}x\ge l^{-1}(\gamma).
--   $$
--   So the feasible set of constraint (4.26) is defined by one deterministic linear inequality, and it is empty when $l^{-1}(\gamma)=+\infty$.
--
--   This is the reason Proposition 4.4 is proved: a constraint on a conditional expectation, nonconvex in general, becomes linear when only the right-hand side is random.
--
--   **Formalization Note** The left side above uses the convention of (4.25), and the mean residual life takes the same value $0$ where $\mathbb P(\xi>s)=0$, so the equality holds for all $x$.
--
--   Differences from the source:
--   - reading: l^{-1}(z) := inf{z | l(z) ≤ γ} → l^{-1}(γ) := inf{s | l(s) ≤ γ}; reason: the printed formula uses z both as argument and as bound variable
--   - encoding: real inf, with no statement about an empty level set → inf in EReal, so inf ∅ = +∞; reason: covers every γ; for a γ with empty level set both sides of the equivalence are false
--   - reading: l(s) defined only where ℙ(ξ > s) > 0 → l(s) = 0 where ℙ(ξ > s) = 0 (the platform's mrl), also inside the level set defining l^{-1}; reason: l(tᵀx) stands for the left side of (4.26), which (4.25) sets to 0 when ℙ(ζ < 0) = 0, so the 0 value is the book's own convention for this constraint
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, eq. (4.26) and the display below Proposition 4.4, p.159

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_mrl
import Definitions.Def_KallMayerSLP_CondExp_rhoCexp
import Definitions.Def_KallMayerSLP_CondExp_mrlInv
import Definitions.Def_LogConcaveOn

open MeasureTheory

namespace KallMayerSLP.CondExp

open StochasticOrders.MeanResidualLife

/-- With `ζ(x, ξ) = tᵀx - ξ` and `ξ` as in Proposition 4.4, the constraint (4.26)
`𝔼[-ζ(x, ξ) | ζ(x, ξ) < 0] ≤ γ` takes the form `l(tᵀx) ≤ γ ⟺ tᵀx ≥ l⁻¹(γ)`, a deterministic linear
constraint.
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, eq. (4.26) and the display below
Proposition 4.4, p.159 (PDF 169).

**Formalization Note** The left side of (4.26) is `rhoCexp` of (4.25), with its `0`-convention; the
platform's `mrl` carries the same convention, so the first clause holds for all `x`. `l⁻¹` is
`EReal`-valued: for `γ` with `{s | l(s) ≤ γ} = ∅` it is `+∞` and the constraint is infeasible, as the
book's `inf ∅ = +∞` gives. The second clause therefore holds for every `γ`. -/
theorem constraint_4_26_linear {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ξ : Ω → ℝ) (hξ : Measurable ξ) (f : ℝ → ℝ)
    (hdens : μ.map ξ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (hlog : ConvexOptimization.LogConcaveOn Set.univ f) (hint : Integrable ξ μ)
    (t : Fin n → ℝ) (γ : ℝ) :
    (∀ x : Fin n → ℝ, rhoCexp μ (fun ω => t ⬝ᵥ x - ξ ω) = mrl μ ξ (t ⬝ᵥ x)) ∧
      ∀ x : Fin n → ℝ, mrl μ ξ (t ⬝ᵥ x) ≤ γ ↔ mrlInv μ ξ γ ≤ ((t ⬝ᵥ x : ℝ) : EReal) := by sorry

end KallMayerSLP.CondExp
