-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_lemma_5_4
-- name    : LinearSetReconciliation327.Main.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:32.523234+00:00
-- url     : https://prove2.me/theorems/261a55c5-6d67-4b4c-89fe-0666f6ed9432
-- title:
--   Lemma 5.4 — HintSketch remaining errors
-- statement:
--   For sufficiently large $A$, then $C$, at a recursive or direct node, for every input and hint satisfying (3): $\mathbb EZ\le\eta(D+1)$, and for $t=\min(N,\lceil2\eta(D+1)\rceil)$, $\Pr[Z>t]\le2^{-\lambda_*}$.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
--   - encoding: sufficiently large absolute A, then sufficiently large C → ∃A₀ ∀A≥A₀ ∃C₀ ∀C≥C₀, before the instance; reason: §5.2 fixes A first and then C
--   - encoding: Pr and E over the node randomness → uniform averages over the finite type of a permutation of [N] and the row coins; reason: this is the source law; coins for indices up to N_max beyond a shorter row are never read
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Lemma 5.4, PDF p.22 (printed p.21)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Lemma 5.4 (Remaining errors), PDF p.22 (printed p.21). `A`, then `C`, are sufficiently large. -/
theorem lemma_5_4 :
    ∃ A₀ : ℕ, ∀ A ≥ A₀, ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ (n lam N X Y : ℕ),
      let P : HintParams := ⟨A, C, n, lam⟩
      P.NodeArgs N X Y → P.NonLeaf N X Y →
      ∀ x J : Finset ℕ, Node.Valid N X Y x J →
        let sch := P.scheme N X Y
        expU (fun lr : sch.LocalSeed => (sch.Z lr x J : ℝ)) ≤
            P.eta * ((HintParams.D N X Y : ℝ) + 1) ∧
        prU (fun lr : sch.LocalSeed => P.resid N X Y < sch.Z lr x J) ≤
            ((2 : ℝ) ^ P.lamStar)⁻¹ := by sorry

end LinearSetReconciliation327.Main
