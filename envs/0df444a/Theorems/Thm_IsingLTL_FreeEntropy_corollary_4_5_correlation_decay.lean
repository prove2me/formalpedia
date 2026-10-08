-- Prove2me | Theorems.Thm_IsingLTL_FreeEntropy_corollary_4_5_correlation_decay
-- name    : IsingLTL.FreeEntropy.corollary_4_5_correlation_decay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:58.972983+00:00
-- url     : https://prove2.me/theorems/f734971d-39ab-438a-911d-b1deb4512cea
-- title:
--   Corollary 4.5, (4.13) — $\mathbb E\{\sum_{i\in\partial T(r)}\langle x_\varnothing;x_i\rangle^{(\ell)}_\varnothing\}\le Ae^{-\lambda r}$
-- statement:
--   Let $T$ be a conditionally independent tree with average offspring numbers bounded by $\Delta$, and $0<B_{\min}\le B_{\max}$, $\beta_{\max}$ finite. There exist $A$ finite and $\lambda>0$, depending only on $\beta_{\max},B_{\min},B_{\max},\Delta$, such that for every such tree, every $0\le\beta\le\beta_{\max}$, every $r\le\ell$ and every field with $B_i\le B_{\max}$ on $T(r-1)$ and $B_i\ge B_{\min}$ on $T(\ell)$,
--   $$\mathbb E\Big\{\sum_{i\in\partial T(r)}\langle x_\varnothing;x_i\rangle^{(\ell)}_\varnothing\Big\}\le Ae^{-\lambda r}.$$
--
--   Correlations between the root and generation $r$ decay exponentially in $r$, in expectation, uniformly in $\ell$.
--
--   **Formalization Note** This item formalizes the first clause (4.13) of the corollary; the second clause (the rate in Theorem 4.2) is not used in this mission. The setting is that of Theorem 4.2; $\langle\cdot\rangle^{(\ell)}_\varnothing$ is the free-boundary measure $\mu^{\ell,0}$. $A,\lambda$ are chosen before the tree law, $\beta$, the field, $r$ and $\ell$. The expectation is a lower integral of the (nonnegative) sum, with measurability part of the conclusion.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 15, Corollary 4.5, (4.13) (first clause); p. 11, Theorem 4.2 (setting)

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_CondIndepTree

namespace IsingLTL.FreeEntropy

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
      ∀ (μ : Measure (List ℕ → ℕ)) [IsProbabilityMeasure μ], IsCondIndepTree μ Δ →
      ∀ (β : ℝ) (B : List ℕ → ℝ) (r ℓ : ℕ), 0 ≤ β → β ≤ βmax → r ≤ ℓ →
        (∀ w : List ℕ, w.length + 1 ≤ r → B w ≤ Bmax) →
        (∀ w : List ℕ, w.length ≤ ℓ → Bmin ≤ B w) →
        Measurable (fun ω => ∑ i ∈ gen ω r, corrOn (ballTree ω ℓ) (isingTree ω β B ℓ false) [] i) ∧
          ∫⁻ ω, ENNReal.ofReal
              (∑ i ∈ gen ω r, corrOn (ballTree ω ℓ) (isingTree ω β B ℓ false) [] i) ∂μ ≤
            ENNReal.ofReal (A * Real.exp (-lam * r)) := by sorry

end IsingLTL.FreeEntropy
