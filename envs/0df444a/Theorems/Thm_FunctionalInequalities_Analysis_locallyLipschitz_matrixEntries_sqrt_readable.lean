-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_locallyLipschitz_matrixEntries_sqrt_readable
-- name    : FunctionalInequalities.Analysis.locallyLipschitz_matrixEntries_sqrt_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:52.835599+00:00
-- url     : https://prove2.me/theorems/5c4697cb-4b3d-46a3-98ab-b78c98b3d26d
-- title:
--   Local Lipschitz Continuity Of Matrix Square Roots
-- statement:
--   This statement establishes local Lipschitz continuity of the canonical matrix square root.
--
--   Let X be a pseudometric space, let M:X→Matrix(ι,ι,ℝ) be continuous, and assume M(x) is positive definite for every x. If the Frobenius-coordinate map
--
--   $$x\mapsto\operatorname{matrixEntries}(M(x))$$
--
--   is locally Lipschitz, then so is
--
--   $$x\mapsto\operatorname{matrixEntries}(\sqrt{M(x)}).$$
--
--   The conclusion uses the canonical functional-calculus square root and the Frobenius norm.
--
--   This result supplies a local regularity principle for positive-definite matrix profiles.
--
--   **Formalization Note** The theorem is stated for finite index types with decidable equality; positivity is pointwise positive definiteness, not merely semidefiniteness.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem locallyLipschitz_matrixEntries_sqrt {X : Type*} [PseudoMetricSpace X]
--       (M : X → Matrix ι ι ℝ) (hM : Continuous M) (hPD : ∀ x, (M x).PosDef)
--       (hInput : LocallyLipschitz (fun x => matrixEntries (M x))) :
--       LocallyLipschitz (fun x => matrixEntries (CFC.sqrt (M x)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Operator/InverseSqrt`](https://prove2.me/theorems/2794bd57-af01-4015-a91a-cb7827d3a533).
--
--   Definition modules: [`Analysis/Matrix/Positivity`](https://prove2.me/theorems/ed2fd089-dbff-4fcc-9c49-b75c2c3c268c).
--
--   Supporting theorems: [`exists_quadraticFloor_of_posDef`](https://prove2.me/theorems/151ec180-9404-48fb-af6c-ada52b2eac65), [`root_difference_bound`](https://prove2.me/theorems/45094b81-6a32-4174-a33a-b96d1b6184f4).
--
--   Previous: [`inverseSqrt_mul_mul_inverseSqrt`](https://prove2.me/theorems/88c3f67d-7fa1-4c20-b7d0-8fa8e80c182a) · Next: [`locallyLipschitz_inverseSqrt_of_contDiff_ringInverse`](https://prove2.me/theorems/23b7714a-0376-441c-80ce-52e55886211f).
--
--   [Source excerpt, lines 166–169](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Operator/InverseSqrt.lean#L166-L169) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Operator/InverseSqrt.lean#L162-L208 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Operator.InverseSqrt`, declaration `FunctionalInequalities.Analysis.locallyLipschitz_matrixEntries_sqrt`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_InverseSqrt

open scoped MatrixOrder RealInnerProductSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem FunctionalInequalities.Analysis.locallyLipschitz_matrixEntries_sqrt_readable {X : Type*} [PseudoMetricSpace X]
    (M : X → Matrix ι ι ℝ) (hM : Continuous M) (hPD : ∀ x, (M x).PosDef)
    (hInput : LocallyLipschitz (fun x => matrixEntries (M x))) :
    LocallyLipschitz (fun x => matrixEntries (CFC.sqrt (M x))) := by sorry
