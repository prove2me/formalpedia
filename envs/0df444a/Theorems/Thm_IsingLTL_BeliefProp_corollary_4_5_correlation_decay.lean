-- Prove2me | Theorems.Thm_IsingLTL_BeliefProp_corollary_4_5_correlation_decay
-- name    : IsingLTL.BeliefProp.corollary_4_5_correlation_decay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:43.678012+00:00
-- url     : https://prove2.me/theorems/1b6eb31b-8d3c-4b74-9dff-2b57f69340a3
-- title:
--   Exponential decay of root–generation correlations (Corollary 4.5, (4.13))
-- statement:
--   Let $0<B_{\min}\le B_{\max}$, and $\beta_{\max}$, $\Delta$ finite. There exist $A<\infty$ and $\lambda>0$, depending only on $\beta_{\max},B_{\min},B_{\max},\Delta$, such that the following holds. Let $\mathsf T$ be a conditionally independent tree with average offspring numbers bounded by $\Delta$, $0\le\beta\le\beta_{\max}$, $r\le\ell$, and $\underline B$ a field with $B_i\le B_{\max}$ on $\mathsf T(r-1)$ and $B_i\ge B_{\min}$ on $\mathsf T(\ell)$. Then
--   $$\mathbb E\Big\{\sum_{i\in\partial\mathsf T(r)}\langle x_\varnothing;x_i\rangle^{(\ell)}_\varnothing\Big\}\le A\,e^{-\lambda r},$$
--   where $\langle\cdot\rangle^{(\ell)}_\varnothing$ is the Ising measure $\mu^{\ell,0}$ on $\mathsf T(\ell)$ with free boundary.
--
--   This is the exponential decay of correlations that drives the exponential rates of Theorems 2.6 and 2.7.
--
--   **Formalization Note** The hypotheses are those of Theorem 4.2. The sum is nonnegative (by Griffiths' inequality), and the expectation is an integral in $[0,\infty]$; measurability of the sum as a function of the tree is part of the conclusion.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 15, Corollary 4.5, eq. (4.13)

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_CondIndepTree

namespace IsingLTL.BeliefProp

open MeasureTheory

/-- **Corollary 4.5, first clause** (Dembo–Montanari, arXiv:0804.4726v3, p. 15, eq. (4.13)). There
exist `A` finite and `λ` positive, depending only on `β_max, B_min, B_max, Δ`, such that
`E{∑_{i∈∂T(r)} ⟨x_ø; x_i⟩^{(ℓ)}_ø} ≤ A e^{−λr}` for any `r ≤ ℓ`.

Formalization Note: the setting is that of Theorem 4.2 (p. 11): `T` a conditionally independent
tree with average offspring numbers bounded by `Δ`, `0 < B_min ≤ B_max`, `0 ≤ β ≤ β_max`,
`B_i ≤ B_max` on `T(r − 1)` and `B_i ≥ B_min` on `T(ℓ)`; `⟨·⟩^{(ℓ)}_ø` is the free-boundary Ising
measure `μ^{ℓ,0}` on `T(ℓ)`. `A, λ` are chosen before the tree law, the field, `β`, `r`, `ℓ`. The
expectation is a lower Lebesgue integral of the (nonnegative, by Griffiths' inequality) sum, with
measurability of the sum part of the conclusion. -/
theorem corollary_4_5_correlation_decay (βmax Bmin Bmax Δ : ℝ) (hBmin : 0 < Bmin)
    (hBB : Bmin ≤ Bmax) :
    ∃ A lam : ℝ, 0 < lam ∧
      ∀ (μ : Measure (List ℕ → ℕ)) [IsProbabilityMeasure μ], IsingLTL.FreeEntropy.IsCondIndepTree μ Δ →
      ∀ (β : ℝ) (B : List ℕ → ℝ) (r ℓ : ℕ), 0 ≤ β → β ≤ βmax → r ≤ ℓ →
        (∀ w : List ℕ, w.length + 1 ≤ r → B w ≤ Bmax) →
        (∀ w : List ℕ, w.length ≤ ℓ → Bmin ≤ B w) →
        Measurable (fun ω => ∑ i ∈ gen ω r, corrOn (ballTree ω ℓ) (isingTree ω β B ℓ false) [] i) ∧
          ∫⁻ ω, ENNReal.ofReal
              (∑ i ∈ gen ω r, corrOn (ballTree ω ℓ) (isingTree ω β B ℓ false) [] i) ∂μ ≤
            ENNReal.ofReal (A * Real.exp (-lam * r)) := by sorry

end IsingLTL.BeliefProp
