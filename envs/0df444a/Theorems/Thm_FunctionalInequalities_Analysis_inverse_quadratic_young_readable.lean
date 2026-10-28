-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_inverse_quadratic_young_readable
-- name    : FunctionalInequalities.Analysis.inverse_quadratic_young_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:51.398388+00:00
-- url     : https://prove2.me/theorems/88b8a40a-52a8-4842-a7d8-a36165a50c94
-- title:
--   Inverse Quadratic Young Inequality
-- statement:
--   This formalizes the inverse-quadratic inequality cited as Lemma A.6 of Letwin (arXiv:2607.24164v1).
--
--   Let ι be a finite index type with decidable equality, let H be a real positive-definite matrix, and let v,w:ι→ℝ. Then
--
--   $$2\,v\mathbin{\cdot}w\leq v\mathbin{\cdot}(H^{-1}v)+w\mathbin{\cdot}(Hw).$$
--
--   This is a finite-dimensional quadratic Young inequality with no identity or commutation restriction on H.
--
--   The result is a standard algebraic estimate for inverse-weighted cross terms.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inverse_quadratic_young
--       {ι : Type*} [Fintype ι] [DecidableEq ι]
--       (H : Matrix ι ι ℝ) (hH : H.PosDef) (v w : ι → ℝ) :
--       2 * (v ⬝ᵥ w) ≤ v ⬝ᵥ (H⁻¹ *ᵥ v) + w ⬝ᵥ (H *ᵥ w)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Positivity`](https://prove2.me/theorems/ed2fd089-dbff-4fcc-9c49-b75c2c3c268c).
--
--   Previous: [`root_difference_bound`](https://prove2.me/theorems/45094b81-6a32-4174-a33a-b96d1b6184f4) · Next: [`trace_mul_nonneg`](https://prove2.me/theorems/8f84fe39-fbf6-4934-8c39-8242968c3544).
--
--   [Source excerpt, lines 292–295](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean#L292-L295) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.6. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean#L291-L334 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Positivity`, declaration `FunctionalInequalities.Analysis.inverse_quadratic_young`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Positivity

open scoped BigOperators Matrix

theorem FunctionalInequalities.Analysis.inverse_quadratic_young_readable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (v w : ι → ℝ) :
    2 * (v ⬝ᵥ w) ≤ v ⬝ᵥ (H⁻¹ *ᵥ v) + w ⬝ᵥ (H *ᵥ w) := by sorry
