-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_memLp_affineOrthPart_readable
-- name    : FunctionalInequalities.L2.memLp_affineOrthPart_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:54.267851+00:00
-- url     : https://prove2.me/theorems/3bf6a5c9-eaa1-466d-aa39-eafd8f3964a0
-- title:
--   Square Integrability of the Affine Residual
-- statement:
--   This statement asserts square integrability of the designated affine residual.
--
--   Let $n\in\mathbb N$, $E=$ `EuclideanSpace ℝ (Fin n)`, and $(e_j)$ its standard orthonormal basis. Let $\mu$ be a probability measure on $E$ with $\operatorname{id}\in L^2(\mu)$, and let $g:E\to\mathbb R$ belong to $L^2(\mu)$. Define $h=$ `L2.affineOrthPart μ g` by
--   $$
--   h(x)=g(x)-\int g\,d\mu-\sum_{j\in\operatorname{Fin}(n)}\left(\int\langle e_j,y\rangle g(y)\,d\mu(y)\right)\langle e_j,x\rangle.
--   $$
--   Then
--   $$
--   h\in L^2(\mu).
--   $$
--   This makes the residual available as an $L^2$ function in subsequent decomposition identities. No centering or identity-covariance assumption is required.
--
--   **Formalization Note** Membership is expressed by `MemLp`, including almost-everywhere strong measurability. All natural dimensions, including zero, are allowed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.L2`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem memLp_affineOrthPart (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
--       (hμ2 : MemLp id 2 μ) {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) :
--       MemLp (affineOrthPart μ g) 2 μ
--   ```
--
--   **Module navigation**
--
--   Module: [`L2/AffineDecomposition`](https://prove2.me/theorems/78e08949-2f1e-4981-ab20-7428c8af6614).
--
--   Previous: [`integral_affineOrthPart`](https://prove2.me/theorems/c7437f0d-1782-4a2e-ab79-cc4f3f38eb24) · Next: [`integral_inner_mul_affineOrthPart`](https://prove2.me/theorems/c43097da-d56f-42d1-8178-075a15d4e395).
--
--   [Source excerpt, lines 245–247](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L245-L247) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L244-L271 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, declaration `FunctionalInequalities.L2.memLp_affineOrthPart`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition

open MeasureTheory
variable {n : ℕ}

theorem FunctionalInequalities.L2.memLp_affineOrthPart_readable (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) :
    MemLp (affineOrthPart μ g) 2 μ := by sorry
