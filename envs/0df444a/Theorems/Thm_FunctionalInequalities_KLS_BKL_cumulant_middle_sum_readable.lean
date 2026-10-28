-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_cumulant_middle_sum_readable
-- name    : FunctionalInequalities.KLS.BKL.cumulant_middle_sum_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:58.080989+00:00
-- url     : https://prove2.me/theorems/9e0a41d8-8c46-4618-8921-3e596dfd076a
-- title:
--   Multilinear Contraction in the Middle Slot
-- statement:
--   This is a finite-dimensional multilinear algebra lemma used to contract a middle tensor slot.
--
--   Let $T:(\mathbb{R}^n)^3\to\mathbb{R}$ be a continuous trilinear map, let $x,z,w\in\mathbb{R}^n$, let $v:\operatorname{Fin}(n)\to\mathbb{R}$, and let $b:\operatorname{Fin}(n)\to\mathbb{R}^n$. If
--
--   $$
--   w=\sum_j v_j b_j,
--   $$
--
--   then
--
--   $$
--   \sum_j T(x,b_j,z)v_j=T(x,w,z).
--   $$
--
--   This auxiliary lemma records linearity in the middle argument and is used to rewrite finite sums of third-order cumulant terms.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma cumulant_middle_sum
--       (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) ℝ)
--       (x z : EuclideanSpace ℝ (Fin n)) (v : Fin n → ℝ)
--       (b : Fin n → EuclideanSpace ℝ (Fin n))
--       (w : EuclideanSpace ℝ (Fin n))
--       (hw : w = ∑ j, v j • b j) :
--       ∑ j, T ![x, b j, z] * v j = T ![x, w, z]
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/NoiseBound`](https://prove2.me/theorems/f9dd651e-3cbd-4d7a-892b-a8785e460e72).
--
--   Next: [`cumulantEnergy_succ_eq`](https://prove2.me/theorems/a8033ec2-2b13-4f3a-8086-a0cc4a62b333).
--
--   [Source excerpt, lines 24–30](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/NoiseBound.lean#L24-L30) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/NoiseBound.lean#L24-L83 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.NoiseBound`, declaration `_private.FunctionalInequalities.KLS.BKL.Localization.NoiseBound.0.FunctionalInequalities.KLS.BKL.cumulant_middle_sum`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_NoiseBound

variable {n : ℕ}

lemma FunctionalInequalities.KLS.BKL.cumulant_middle_sum_readable
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) ℝ)
    (x z : EuclideanSpace ℝ (Fin n)) (v : Fin n → ℝ)
    (b : Fin n → EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n))
    (hw : w = ∑ j, v j • b j) :
    ∑ j, T ![x, b j, z] * v j = T ![x, w, z] := by sorry
