-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_lemma_5_6
-- name    : LinearSetReconciliation327.Main.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:35.680226+00:00
-- url     : https://prove2.me/theorems/9dcc8326-b055-4452-a8f7-59b5a533aedb
-- title:
--   Lemma 5.6 — HintSketch sufficient child capacities
-- statement:
--   For sufficiently large $A$, then $C$, at a recursive node, every input and hint satisfying (3) and every column $s$: $\mathbb EU_s\le Q_s+D\eta^2$, $\mathbb EV_s\le2^{-c}Q_s+D\eta^2$, and with the capacities (19) each of $U_s>X_s$, $V_s>Y_s$ has probability at most $2^{-\lambda_*}$.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
--   - encoding: sufficiently large absolute A, then sufficiently large C → ∃A₀ ∀A≥A₀ ∃C₀ ∀C≥C₀, before the instance; reason: §5.2 fixes A first and then C
--   - encoding: Pr and E over the node randomness → uniform averages over the finite type of a permutation of [N] and the row coins; reason: this is the source law; coins for indices up to N_max beyond a shorter row are never read
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Lemma 5.6, PDF p.23 (printed p.22)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Lemma 5.6 (Sufficient child capacities), PDF p.23 (printed p.22). The source's column `s` is
`s + 1` here. `A`, then `C`, are sufficiently large. -/
theorem lemma_5_6 :
    ∃ A₀ : ℕ, ∀ A ≥ A₀, ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ (n lam N X Y : ℕ),
      let P : HintParams := ⟨A, C, n, lam⟩
      P.NodeArgs N X Y → P.rule N X Y = .recursive →
      ∀ x J : Finset ℕ, Node.Valid N X Y x J →
        let sch := P.scheme N X Y
        ∀ s : Fin sch.ℓ,
          expU (fun lr : sch.LocalSeed => (sch.U lr x J s : ℝ)) ≤
            P.Q N X Y s.val + (HintParams.D N X Y : ℝ) * P.eta ^ 2 ∧
          expU (fun lr : sch.LocalSeed => (sch.V lr x J s : ℝ)) ≤
            ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s.val + (HintParams.D N X Y : ℝ) * P.eta ^ 2 ∧
          prU (fun lr : sch.LocalSeed => P.capX N X Y s.val < sch.U lr x J s) ≤
            ((2 : ℝ) ^ P.lamStar)⁻¹ ∧
          prU (fun lr : sch.LocalSeed => P.capY N X Y s.val < sch.V lr x J s) ≤
            ((2 : ℝ) ^ P.lamStar)⁻¹ := by sorry

end LinearSetReconciliation327.Main
