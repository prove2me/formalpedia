-- Prove2me | Theorems.Thm_GibbsTransition_SizeCopies_Supplement_reconstruction_local_terms
-- name    : GibbsTransition.SizeCopies.Supplement.reconstruction_local_terms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:40:30.592273+00:00
-- url     : https://prove2.me/theorems/5ba02776-a3e0-4572-9cdf-53b3fdaa75b6
-- title:
--   Lemma 6.1 — Local-term reconstruction
-- statement:
--   For each finite local dimension $q\ge1$, a bounded linear map, depending only on $q$, recovers the canonical on-site term $g_\infty$ and three connected edge terms $G_i$ from the trace-free one-site and side-two bulk Hamiltonians. For Hermitian input estimates with operator-norm errors at most $\nu\ge0$,
--   $$\|\widehat g_\infty-g_\infty\|\le3\nu,\qquad\|\widehat G_i-G_i\|\le3\nu\quad(i=1,2,3),$$
--   and the resulting finite ground-energy density error is at most $12\nu$, for every positive cube size. The recovered interaction equals the canonical interaction on the exact inputs.
--
--   Normalized partial traces and the same directed edge convention define this single shared recovery map. Errors are measured against the exact trace-free Hamiltonians. Hermitian estimates may retain scalar trace error; no additional trace-removal operation or loss is inserted.
--
--   Differences from the source:
--   - encoding: bounded linear recovery and energy-density error → a continuous complex-linear map and finite-volume spectral energy-density error; reason: finite-dimensional bounded linear maps are continuous; the variational norm bound gives the same density error
--   - generalization: algebraic bounded source interactions and the public effect on the control interval, with trace-free estimated inputs → exact recovery for arbitrary complex local matrices, and perturbation bounds for Hermitian local matrices with any Hermitian effect and every real field, allowing Hermitian estimated inputs with residual scalar trace; reason: the partial-trace identities are complex-linear and the perturbation estimate is independent of algebraicity, the field value and the common unchanged effect; restricting to the source data recovers every original instance; each recovery component is a sum of three norm contractions, so the same 3 nu and 12 nu bounds also cover residual scalar errors
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Lemma 6.1, printed p. 13 (PDF p. 15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Supplement_Recovery
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false

namespace GibbsTransition.SizeCopies.Supplement

theorem reconstruction_local_terms (q : ℕ) (hq : 0 < q) :
    ∃ (M : ℝ) (T : (Local q × Cube q 2) →L[ℂ] (Local q × (Fin 3 → Pair q))),
      0 < M ∧ ‖T‖ ≤ M ∧
      (∀ X1 X2, T (X1,X2) = (recoveredOnsite X1 X2,recoveredEdge X2)) ∧
      ∀ u : FieldInteraction q,
        recovered (traceFree u.onsite) (traceFree (fieldBulk u 2)) = canonical u ∧
        ∀ (X1 : Local q) (X2 : Cube q 2) (nu : ℝ),
          u.onsite.IsHermitian → (∀ i, (u.edge i).IsHermitian) →
          X1.IsHermitian → X2.IsHermitian → 0 ≤ nu →
          ‖X1-traceFree u.onsite‖ ≤ nu → ‖X2-traceFree (fieldBulk u 2)‖ ≤ nu →
          ‖recoveredOnsite X1 X2-(canonical u).onsite‖ ≤ 3*nu ∧
          (∀ i, ‖recoveredEdge X2 i-(canonical u).edge i‖ ≤ 3*nu) ∧
          ∀ (P : Local q), P.IsHermitian → ∀ (L : ℕ), 1 ≤ L → ∀ phi : ℝ,
            |canonicalEnergy (recovered X1 X2) P L phi -
              canonicalEnergy (canonical u) P L phi| ≤ 12*nu := by sorry

end GibbsTransition.SizeCopies.Supplement
