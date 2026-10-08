-- Prove2me | Theorems.Thm_McLeishCLT_MDA_trunc_prodT_uniformIntegrable
-- name    : McLeishCLT.MDA.trunc_prodT_uniformIntegrable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:32:53.754203+00:00
-- url     : https://prove2.me/theorems/41b31028-7d9d-425e-ae95-fcc7b938954a
-- title:
--   p. 622, proof of (2.3) — {T_n} built from the truncated array is uniformly integrable
-- statement:
--   Let $\{X_{n,i}\}$ be a martingale difference array with respect to row-wise filtrations $\{\mathcal F_{n,i}\}$ such that $\max_{i\le k_n}|X_{n,i}|$ is uniformly bounded in $L_2$ norm, i.e. there is $C<\infty$ with
--   $$\Big\|\max_{i\le k_n}|X_{n,i}|\Big\|_2\le C\quad\text{for all }n .$$
--   Let $Z_{n,j}=X_{n,j}\,I(\sum_{k=1}^{j-1}X_{n,k}^2\le2)$ and $T_n=\prod_{j=1}^{k_n}(1+itZ_{n,j})$. Then for every real $t$ the family $\{T_n\}_n$ is uniformly integrable.
--
--   This verifies condition (2.1 b) for the truncated array in the proof of Theorem (2.3).
--
--   **Formalization Note** Uniform integrability is Mathlib's `UniformIntegrable … 1 P`: a.e. strong measurability, a uniform $L_1$ bound, and uniformly small tails.
-- source:
--   McLeish, Dependent central limit theorems and invariance principles, Ann. Probab. 2 (1974), p. 622, proof of Theorem (2.3), "Therefore, {T_n} is uniformly integrable"

import Mathlib
import Definitions.Def_McLeishCLT_MDA_Setting

namespace McLeishCLT.MDA

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- p. 622, proof of (2.3): `{T_n}` built from the truncated array is uniformly integrable. -/
theorem trunc_prodT_uniformIntegrable {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : ℕ → Filtration ℕ m0) (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ)
    (hmda : IsMDA P ℱ k X)
    (ha : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n, eLpNorm (maxAbs k X n) 2 P ≤ C) :
    ∀ t : ℝ, UniformIntegrable (fun n => prodT k (trunc X) t n) 1 P := by sorry

end McLeishCLT.MDA
