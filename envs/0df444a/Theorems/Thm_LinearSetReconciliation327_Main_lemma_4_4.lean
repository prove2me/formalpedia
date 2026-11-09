-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_lemma_4_4
-- name    : LinearSetReconciliation327.Main.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:40.276226+00:00
-- url     : https://prove2.me/theorems/aafea5d4-cfeb-4092-ada4-69651a647ff8
-- title:
--   Lemma 4.4 — Entropy and total mass
-- statement:
--   For a finite family of nonnegative $q_i$ with $0<Q=\sum_iq_i\le N$, $\sum_ih_N(q_i)=h_N(Q)+QH((q_i/Q)_i)$. For $u,v\ge0$ with $u+v\le N$, $h_N(u+v)\le h_N(u)+h_N(v)$.
--
--   Differences from the source: none.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Lemma 4.4, PDF p.17 (printed p.16)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Lemma 4.4 (Entropy and total mass), PDF p.17 (printed p.16). -/
theorem lemma_4_4 (N : ℕ) :
    (∀ (ι : Type) [Fintype ι] (q : ι → ℝ), (∀ i, 0 ≤ q i) → 0 < ∑ i, q i → ∑ i, q i ≤ N →
      ∑ i, hN N (q i) =
        hN N (∑ i, q i) + (∑ i, q i) * entropyFin (fun i => q i / ∑ i', q i')) ∧
    (∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u + v ≤ N → hN N (u + v) ≤ hN N u + hN N v) := by sorry

end LinearSetReconciliation327.Main
