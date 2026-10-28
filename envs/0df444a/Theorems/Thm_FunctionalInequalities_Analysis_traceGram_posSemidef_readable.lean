-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_traceGram_posSemidef_readable
-- name    : FunctionalInequalities.Analysis.traceGram_posSemidef_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:51.969492+00:00
-- url     : https://prove2.me/theorems/244506ec-0037-4420-8e3c-8acdf6db2119
-- title:
--   Positive Semidefinite Trace Gram Matrix
-- statement:
--   This formalizes part of Theorem 2.5 of Letwin (arXiv:2607.24164v1), cited there as the key moment-map Hessian bound.
--
--   Let ι and κ be finite index types. Let B be a real positive semidefinite matrix on ι, and let Tₐ be a family of symmetric real matrices indexed by κ. Define the κ-by-κ matrix
--
--   $$G_{ab}=\operatorname{tr}(B T_a B T_b).$$
--
--   Then G is positive semidefinite.
--
--   The result provides a trace-weighted Gram-matrix formulation useful for controlling families of symmetric derivative matrices.
--
--   **Formalization Note** The statement is purely finite-dimensional and algebraic; it does not itself assert the probabilistic expectation inequality reviewed for the cited paper item.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem traceGram_posSemidef {ι κ : Type*} [Fintype ι] [Fintype κ]
--       (B : Matrix ι ι ℝ) (hB : B.PosSemidef)
--       (T : κ → Matrix ι ι ℝ) (hT : ∀ a, (T a).IsSymm) :
--       (Matrix.of fun a b => (B * T a * B * T b).trace).PosSemidef
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Positivity`](https://prove2.me/theorems/ed2fd089-dbff-4fcc-9c49-b75c2c3c268c).
--
--   Supporting theorems: [`posSemidef_weightedGram`](https://prove2.me/theorems/b7c15040-db81-4850-95bc-cc1e4b6e1569).
--
--   Previous: [`trace_mul_nonneg`](https://prove2.me/theorems/8f84fe39-fbf6-4934-8c39-8242968c3544) · Next: [`trace_forcing_add_twice_energy_nonneg`](https://prove2.me/theorems/880bf0da-cd46-42c8-89a4-a8d488e0bf20).
--
--   [Source excerpt, lines 386–389](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean#L386-L389) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean#L384-L449 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Positivity`, declaration `FunctionalInequalities.Analysis.traceGram_posSemidef`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Positivity

theorem FunctionalInequalities.Analysis.traceGram_posSemidef_readable {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef)
    (T : κ → Matrix ι ι ℝ) (hT : ∀ a, (T a).IsSymm) :
    (Matrix.of fun a b => (B * T a * B * T b).trace).PosSemidef := by sorry
