-- Prove2me | Theorems.Thm_IsingLTL_BeliefProp_corollary_4_5_root_magnetization_rate
-- name    : IsingLTL.BeliefProp.corollary_4_5_root_magnetization_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:19:08.522314+00:00
-- url     : https://prove2.me/theorems/7644cb56-f27b-4e97-a29e-b602513bfd55
-- title:
--   Root magnetizations under plus and free boundary differ by $Ae^{-\lambda\ell}$ (Corollary 4.5, proof)
-- statement:
--   Let $0<B_{\min}\le B_{\max}$, and $\beta_{\max}$, $\Delta$ finite. There exist $A<\infty$ and $\lambda>0$, depending only on $\beta_{\max},B_{\min},B_{\max},\Delta$, such that the following holds. Let $\mathsf T$ be a conditionally independent tree with average offspring numbers bounded by $\Delta$, $0\le\beta\le\beta_{\max}$, $\ell\ge0$, and $\underline B$ a field with $B_i\le B_{\max}$ for all $i\in\mathsf T(\ell-1)$ and $B_i\ge B_{\min}$ for all $i\in\mathsf T(\ell)$. Then
--   $$\mathbb E\big\{m^{\ell,+}(\underline B)-m^{\ell,0}(\underline B)\big\}\le A\,e^{-\lambda\ell}.$$
--
--   This is the bound (4.5) of Lemma 4.3 with the rate $M/\ell$ improved to $Ae^{-\lambda\ell}$, which the proof of Corollary 4.5 establishes ("the rate $\delta(t)$ in Theorem 4.2 is merely the rate in the bound (4.5)"). It is the form used, for deterministic computation trees, in the proofs of Theorems 2.6 and 2.7.
--
--   **Formalization Note** Measurability of $m^{\ell,+}-m^{\ell,0}$ as a function of the tree is part of the conclusion.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, pp. 16–17, proof of Corollary 4.5 (the bound (4.5) with rate A exp(−λℓ), via (4.13) and (4.15))

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_CondIndepTree

namespace IsingLTL.BeliefProp

open MeasureTheory

/-- **Corollary 4.5, root-magnetization form** (Dembo–Montanari, arXiv:0804.4726v3, proof of
Corollary 4.5, p. 16: "recall that the rate `δ(t)` in Theorem 4.2 is merely the rate in the
bound (4.5)"). There exist `A` finite and `λ > 0`, depending only on `β_max, B_min, B_max, Δ`,
such that `E{m^{ℓ,+}(B) − m^{ℓ,0}(B)} ≤ A e^{−λℓ}`: the bound (4.5) of Lemma 4.3 with the rate
`M/ℓ` improved to `A exp(−λℓ)`, under `B_i ≤ B_max` on `T(ℓ − 1)`.

Formalization Note: setting of Theorem 4.2: conditionally independent tree with average
offspring numbers bounded by `Δ`, `0 < B_min ≤ B_max`, `0 ≤ β ≤ β_max`, `B_i ≥ B_min` on `T(ℓ)`,
`B_i ≤ B_max` on `T(ℓ − 1)`; every `ℓ ≥ 0`. This is the form the proofs of Theorems 2.6 and 2.7
(§5) use. Measurability of `ω ↦ m^{ℓ,+} − m^{ℓ,0}` is part of the conclusion. -/
theorem corollary_4_5_root_magnetization_rate (βmax Bmin Bmax Δ : ℝ) (hBmin : 0 < Bmin)
    (hBB : Bmin ≤ Bmax) :
    ∃ A lam : ℝ, 0 < lam ∧
      ∀ (μ : Measure (List ℕ → ℕ)) [IsProbabilityMeasure μ], IsingLTL.FreeEntropy.IsCondIndepTree μ Δ →
      ∀ (β : ℝ) (B : List ℕ → ℝ) (ℓ : ℕ), 0 ≤ β → β ≤ βmax →
        (∀ w : List ℕ, w.length + 1 ≤ ℓ → B w ≤ Bmax) →
        (∀ w : List ℕ, w.length ≤ ℓ → Bmin ≤ B w) →
        Measurable (fun ω => rootMag ω β B ℓ true - rootMag ω β B ℓ false) ∧
          ∫ ω, (rootMag ω β B ℓ true - rootMag ω β B ℓ false) ∂μ ≤ A * Real.exp (-lam * ℓ) := by sorry

end IsingLTL.BeliefProp
