-- Prove2me | Theorems.Thm_LowRandomnessDP_KNorm_lemma_3_8
-- name    : LowRandomnessDP.KNorm.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:31.196375+00:00
-- url     : https://prove2.me/theorems/a4c21a73-bb68-4b2d-a2df-10767aba5664
-- title:
--   Lemma 3.8 — local MSSP cell counts
-- statement:
--   Let $\mathcal P$ be a $(k_d,\rho)$-MSSP and let $m,\lambda\ge0$ satisfy $k_d(\ell)\le m e^{\lambda/\ell}$ for $1\le\ell\le d$. For every $y\in\mathbb R^d$ and $1/d\le\gamma\le1$,
--
--   $$|\mathcal P_{<\gamma}(y)|\le m e^{2\lambda\gamma}.$$
--
--   This controls the strictly nearby cells between the discrete reciprocal scales.
--
--   Differences from the source:
--   - encoding: real vectors and their K-norm → Fin d → ℝ with the Minkowski gauge of the exact compact convex symmetric absorbing disk; reason: coordinate encoding preserves all real vectors and all source norms; compactness excludes nontrivial linear subspaces
--   - encoding: cardinality of a cell collection → a bound on the cardinality of every finite subset; reason: equivalent to the finite cardinal bound and cannot assign zero to an infinite set
--   - generalization: k_d(ℓ)=m(d) exp(λ(d)/ℓ) → k_d(ℓ)≤m exp(lam/ℓ), with m,lam the values at this dimension; reason: a real upper envelope suffices and includes every equality instance without requiring real exponentials to be integers
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf, Lemma 3.8, PDF page 14 / printed page 12

import Definitions.Def_LowRandomnessDP_KNorm_Sampling

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace LowRandomnessDP.KNorm

theorem lemma_3_8 {d : ℕ} (K : Set (Vec d)) (hK : IsBody K)
    (P : CellPartition d) (k : ℕ → ℕ) (ρ : ℝ) (hP : IsMSSP K P k ρ)
    (m lam : ℝ) (hm : 0 ≤ m) (hlam : 0 ≤ lam)
    (hk : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ d → (k ℓ : ℝ) ≤ m * Real.exp (lam / ℓ))
    (y : Vec d) (γ : ℝ) (hγlo : 1 / (d : ℝ) ≤ γ) (hγhi : γ ≤ 1) :
    CountLe (nearCells K P ρ γ y) (m * Real.exp (2 * lam * γ)) := by sorry

end LowRandomnessDP.KNorm
