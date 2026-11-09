-- Prove2me | Theorems.Thm_MinCostMaj_lemma_cost_truncated
-- name    : MinCostMaj.lemma_cost_truncated
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:16:13.581624+00:00
-- url     : https://prove2.me/theorems/1da4ef20-4b36-46d7-8de1-3a08a74df001
-- title:
--   Lemma "Cost of any solution of the truncated instance" — $\mathbb E[\mathrm{cost}]\le C'\sum_v\sum_a c_v(a)\lambda_v(a)$
-- statement:
--   There is a constant $C'=C'(\mathbf A)$ with the following property. Let $V$ be a finite set of variables with potatoes $A^J_v$, LP marginals $\lambda_v$ (probability vectors on $A^J_v$) and finite costs $c_v\ge0$, and let $\alpha$ be any solution of the random truncated instance $I$ (with potatoes $A^I_v=\{a\in A^J_v:\lambda_v(a)\ge t_{L(v)}\}$). Then
--   $$\mathbb E\Big[\sum_v c_v(\alpha(v))\Big]\le C'\sum_v\sum_{a\in A^J_v}c_v(a)\,\lambda_v(a).$$
--
--   With $\mathrm{BLP}(J)\le\mathrm{OPT}$ this gives the constant-factor guarantee in expectation (Proposition 5.3).
--
--   Differences from the source:
--   - generalization: assume that I has a solution; α any solution of I → any assignment α(t) with α(t)(v) in the truncated potato A^I_v(t) for every threshold sequence t in the sampling range; no assumption that a solution exists; reason: every solution of the truncated instance takes values in its potatoes, so the printed statement is the special case of solutions
--   - generalization: costs c_v : A → Q≥0 (∞ values removed before the BLP) → costs c_v : A → ℝ≥0; reason: rational costs are real costs
--   - encoding: E[·] → the lower Lebesgue integral over `thresholdMeasure`, in [0, ∞]; reason: same expectation for a nonnegative cost
--   - encoding: LP marginal λ_v → any probability vector on A^J_v; reason: the BLP marginals are such vectors
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Lemma "Cost of any solution of the truncated instance", p.22 (PDF p.23)

import Mathlib
import Definitions.Def_MinCostMaj_Levels
import Definitions.Def_MinCostMaj_thresholdLaw

namespace MinCostMaj

open MeasureTheory

/-- **Lemma "Cost of any solution of the truncated instance"**, p.22 (PDF p.23).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, p.22: "Assume that I has a solution. Let α be any solution of I. Then
E[Σ_v cv(α(v))] ≤ C′ Σ_v Σ_{a∈A^J_v} cv(a)λv(a), where C′ = C′(A)."

For every domain size `d` there is `C′` such that: for every finite variable set `V`, potatoes
`A^J_v = S v`, LP marginals `λᵥ` (probability vectors on `S v`) and finite costs `cᵥ`, and every
random assignment `α(t)` that takes, for every threshold sequence `t` in the support of the
threshold law, values in the truncated potatoes `A^I_v(t)`, the expected cost is at most
`C′ Σ_v Σ_{a ∈ A^J_v} cᵥ(a) λᵥ(a)`.

**Formalization Note.** Every solution of the truncated instance `I` takes values in its potatoes,
so the statement covers every solution `α(t)` of `I` (and needs no assumption that one exists).
Costs are finite (`ℝ≥0`): values of infinite cost are removed before the BLP is solved (p.5).
The expectation is the lower Lebesgue integral in `ℝ≥0∞`. `C′` depends only on `|A|`. -/
theorem lemma_cost_truncated :
    ∀ d : ℕ, ∃ C' : ℝ, ∀ (V : Type) [Fintype V] (S : V → Finset (Fin d))
      (lam : V → Fin d → ℝ) (c : V → Fin d → NNReal), (∀ v, IsProbVec (S v) (lam v)) →
      ∀ α : (ℕ → ℝ) → V → Fin d,
        (∀ t : ℕ → ℝ, (∀ i, 1 ≤ i → ((1 : ℝ) / 2) ^ i ≤ t i ∧ t i ≤ 2 * ((1 : ℝ) / 2) ^ i) →
          ∀ v, α t v ∈ truncPot (S v) (lam v) t) →
        ∫⁻ t, ∑ v, (c v (α t v) : ENNReal) ∂thresholdMeasure ≤
          ENNReal.ofReal C' * ∑ v, ∑ a ∈ S v, (c v a : ENNReal) * ENNReal.ofReal (lam v a) := by sorry

end MinCostMaj
