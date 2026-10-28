-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_card_slots_readable
-- name    : FunctionalInequalities.Analysis.Tensor.card_slots_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:58.871231+00:00
-- url     : https://prove2.me/theorems/bb7f2252-e4b8-450e-8add-eea118a83e46
-- title:
--   Cardinality of an Index Interval
-- statement:
--   This is an elementary cardinality identity for coordinate slots.
--
--   For natural numbers $a,b,k$ with $b\le k$, let `slots k a b` be the positions $p\in\operatorname{Fin}(k)$ satisfying $a\le p<b$. Then
--
--   $$
--   |\operatorname{slots}(k,a,b)|=b-a.
--   $$
--
--   The result is used to verify the sizes of the coordinate blocks in the tensor symmetrization theorem.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem card_slots {k a b : ℕ} (hb : b ≤ k) : (slots k a b).card = b - a
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Coordinate`](https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f).
--
--   Next: [`norm_le_four_pow_mul_norm_symmetrize`](https://prove2.me/theorems/f0e3d670-24f7-4ef8-927b-cc5e41de1898).
--
--   [Source excerpt, lines 65–65](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Coordinate.lean#L65-L65) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Coordinate.lean#L64-L83 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Coordinate`, declaration `FunctionalInequalities.Analysis.Tensor.card_slots`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coordinate

theorem FunctionalInequalities.Analysis.Tensor.card_slots_readable {k a b : ℕ} (hb : b ≤ k) : (slots k a b).card = b - a := by sorry
