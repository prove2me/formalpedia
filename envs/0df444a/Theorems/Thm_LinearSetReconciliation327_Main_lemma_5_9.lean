-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_lemma_5_9
-- name    : LinearSetReconciliation327.Main.lemma_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:46.400209+00:00
-- url     : https://prove2.me/theorems/e72a9a7a-cdbf-4f6f-8d0c-eb73ba344c12
-- title:
--   Lemma 5.9 — Child space and density contraction
-- statement:
--   For a CR family with $\mathrm{rows}\le K_{CR}t\log^2(N+2)$ there is $K$ such that for sufficiently large $A$, then $C$, at a recursive node: $\sum_sX_s\le X+KCh_N(Y)$, $\sum_sh_Y(Y_s)\le\frac14h_N(Y)$, $\sum_s\rho_s\le\rho/4$ with $\rho=Y/N$, $\rho_s=Y_s/Y$; and $\sum_{s\text{ recursive}}(X_s+C^2h_Y(Y_s))+\sum_{s\text{ direct}}X_s+\sum_{s\text{ cheap}}\mathrm{Len}_{CR}(s)\le X+C^2h_N(Y)$, where children are classified by the stopping rules and small-instance leaves are excluded as in the source.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
--   - encoding: O-notation with absolute constants → explicit absolute constants and exponents quantified before all instance parameters; reason: §2.1: unless stated otherwise constants are absolute
--   - encoding: sufficiently large absolute A, then sufficiently large C → ∃A₀ ∀A≥A₀ ∃C₀ ∀C≥C₀, before the instance; reason: §5.2 fixes A first and then C
--   - encoding: Len_CR(s), the length of the CR sketch of Proposition 2.3 → rows of any CR family with the row bound of Proposition 2.3; reason: the source proof uses only this row bound
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Lemma 5.9, PDF p.24 (printed p.23)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

open Classical in
/-- Lemma 5.9 (Child space and density contraction), PDF p.24 (printed p.23). The hidden constant `K`
of `O(C h_N(Y))` precedes `A` and `C`. `Len_CR(s)` is the actual length of the child's CR sketch for
a CR family with the row bound of Proposition 2.3. -/
theorem lemma_5_9 (KCR : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ A₀ : ℕ, ∀ A ≥ A₀, ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ (n lam N X Y : ℕ) (CR : CRFamily),
      (∀ N' t : ℕ, t ≤ N' → (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2)) →
      let P : HintParams := ⟨A, C, n, lam⟩
      P.NodeArgs N X Y → P.rule N X Y = .recursive →
      let I := range (P.ell N X Y)
      let Xs := P.capX N X Y
      let Ys := P.capY N X Y
      (∑ s ∈ I, (Xs s : ℝ) ≤ (X : ℝ) + K * ((C : ℝ) * hN N Y)) ∧
      (∑ s ∈ I, hN Y (Ys s) ≤ hN N Y / 4) ∧
      (∑ s ∈ I, ((Ys s : ℝ) / (Y : ℝ)) ≤ ((Y : ℝ) / (N : ℝ)) / 4) ∧
      (∑ s ∈ I.filter (fun s => P.rule Y (Xs s) (Ys s) = .recursive),
            ((Xs s : ℝ) + (C : ℝ) ^ 2 * hN Y (Ys s)) +
          ∑ s ∈ I.filter (fun s => P.rule Y (Xs s) (Ys s) = .direct), (Xs s : ℝ) +
          ∑ s ∈ I.filter (fun s => P.rule Y (Xs s) (Ys s) = .cheap),
            (CR.rows Y (HintParams.D Y (Xs s) (Ys s)) : ℝ) ≤
        (X : ℝ) + (C : ℝ) ^ 2 * hN N Y) := by sorry

end LinearSetReconciliation327.Main
