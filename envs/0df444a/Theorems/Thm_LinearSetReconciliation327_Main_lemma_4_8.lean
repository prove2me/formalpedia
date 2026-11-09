-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_lemma_4_8
-- name    : LinearSetReconciliation327.Main.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:31.013471+00:00
-- url     : https://prove2.me/theorems/02bacfd6-a18f-46c0-a2d2-b17668d9a44a
-- title:
--   Lemma 4.8 — Concentration of column counts and residual
-- statement:
--   Fix a node's input $x$ and hint $J$, with $m\ge1$ rows and $D\ge m$, $|J\cup\mathrm{supp}(x)|\le D$. If each final row estimate of the exact execution has at most $K\ge1$ positions, then for all $\Delta>0$ and columns $s$: $\Pr[U_s>\mathbb EU_s+\Delta]\le\exp(-2\Delta^2/(5D))$, $\Pr[V_s>\mathbb EV_s+\Delta]\le\exp(-2\Delta^2/(5D))$, and $\Pr[Z>\mathbb EZ+\Delta]\le\exp(-\Delta^2/(10DK^2))$.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
--   - generalization: a node of the top layer or of HintSketch → any RowScheme: any row code, prediction and final-recovery procedures; reason: the proof uses only that a row reads its local support, local hint and coins; both constructions are RowSchemes, so the source claim is an instance
--   - encoding: Pr and E over the node randomness → uniform averages over the finite type of a permutation of [N] and the row coins; reason: this is the source law; coins for indices up to N_max beyond a shorter row are never read
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Lemma 4.8, PDF p.18 (printed p.17)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Lemma 4.8 (Concentration), PDF p.18 (printed p.17), for a node of any row scheme. -/
theorem lemma_4_8 (sch : RowScheme) (x J : Finset ℕ) (hx : x ⊆ range sch.N) (hJ : J ⊆ range sch.N)
    (hm : 1 ≤ sch.m) (D : ℕ) (hD : sch.m ≤ D) (hDJ : (J ∪ x).card ≤ D) (K : ℕ) (hK : 1 ≤ K)
    (hest : ∀ (lr : sch.LocalSeed) (j : Fin sch.m), (sch.exactRowEst lr x J j).card ≤ K)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    (∀ s : Fin sch.ℓ,
      prU (fun lr : sch.LocalSeed => expU (fun lr' : sch.LocalSeed => (sch.U lr' x J s : ℝ)) + Δ <
          (sch.U lr x J s : ℝ)) ≤ Real.exp (-(2 * Δ ^ 2 / (5 * (D : ℝ))))) ∧
    (∀ s : Fin sch.ℓ,
      prU (fun lr : sch.LocalSeed => expU (fun lr' : sch.LocalSeed => (sch.V lr' x J s : ℝ)) + Δ <
          (sch.V lr x J s : ℝ)) ≤ Real.exp (-(2 * Δ ^ 2 / (5 * (D : ℝ))))) ∧
    prU (fun lr : sch.LocalSeed => expU (fun lr' : sch.LocalSeed => (sch.Z lr' x J : ℝ)) + Δ <
        (sch.Z lr x J : ℝ)) ≤ Real.exp (-(Δ ^ 2 / (10 * (D : ℝ) * (K : ℝ) ^ 2))) := by sorry

end LinearSetReconciliation327.Main
