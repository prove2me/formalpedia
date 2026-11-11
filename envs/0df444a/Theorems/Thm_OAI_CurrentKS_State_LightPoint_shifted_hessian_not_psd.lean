-- Prove2me | Theorems.Thm_OAI_CurrentKS_State_LightPoint_shifted_hessian_not_psd
-- name    : OAI.CurrentKS.State.LightPoint.shifted_hessian_not_psd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:06.996244+00:00
-- url     : https://prove2.me/theorems/e94d2dd1-8bea-4698-9d48-e0625136ec3b
-- title:
--   OAI.CurrentKS.State.LightPoint.shifted_hessian_not_psd: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.State.LightPoint`, with `open Matrix`, `open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Difference`, `open scoped BigOperators Topology ContDiff`):
--
--   ```lean
--   theorem shifted_hessian_not_psd [NeZero d] [NeZero N] {lam a : ℝ}
--       (ha : 0 < a) (hrel : lam=512*a*p.C1^2)
--       (test : Coordinates N → ℝ)
--       (hgrad : ∀ i,|fderiv ℝ (p.Psi lam) p.x (Pi.single i (1:ℝ))| ≤ a)
--       (herr : ∀ u,|test u-fderiv ℝ (fderiv ℝ (p.Psi lam)) p.x u u| ≤ a/16*(∑ i,u i^2)) :
--       ¬∀ u,test u+7*a*(∑ i,u i^2) ≥ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.State.Coordinates`, `OAI.CurrentKS.State.LightPoint`, `OAI.CurrentKS.State.LightPoint.C1` and `OAI.CurrentKS.State.LightPoint.Psi` (definitions bundle `OAIQ241TT002` of this split).
--
--   **Used by.** The proof of `OAI.CurrentKS.State.LightPoint.computed_candidates_progress` of this split imports it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ241TT002

section

attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State.LightPoint
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Difference
open scoped BigOperators Topology ContDiff

variable {d N : ℕ} (p : LightPoint d N)

theorem shifted_hessian_not_psd [NeZero d] [NeZero N] {lam a : ℝ}
    (ha : 0 < a) (hrel : lam=512*a*p.C1^2)
    (test : Coordinates N → ℝ)
    (hgrad : ∀ i,|fderiv ℝ (p.Psi lam) p.x (Pi.single i (1:ℝ))| ≤ a)
    (herr : ∀ u,|test u-fderiv ℝ (fderiv ℝ (p.Psi lam)) p.x u u| ≤ a/16*(∑ i,u i^2)) :
    ¬∀ u,test u+7*a*(∑ i,u i^2) ≥ 0 := by
  sorry

end
end CurrentKS.State.LightPoint

end OAI
end
