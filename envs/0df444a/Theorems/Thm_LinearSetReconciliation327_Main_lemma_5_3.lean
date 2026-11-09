-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_lemma_5_3
-- name    : LinearSetReconciliation327.Main.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:48.395082+00:00
-- url     : https://prove2.me/theorems/df8df22f-cd68-4e1a-81fe-6d17e32c956f
-- title:
--   Lemma 5.3 — HintSketch row recovery
-- statement:
--   For sufficiently large $A$, then $C$, at a recursive or direct node: for a regular row, final recovery on the true transcript differs from $S_j$ with probability at most $\eta^2/8$; and for an input and hint satisfying (3), the expected number of coordinates of $J\cup\mathrm{supp}(x)$ in overloaded rows is at most $D\eta^2$.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
--   - encoding: O-notation with absolute constants → explicit absolute constants and exponents quantified before all instance parameters; reason: §2.1: unless stated otherwise constants are absolute
--   - encoding: sufficiently large absolute A, then sufficiently large C → ∃A₀ ∀A≥A₀ ∃C₀ ∀C≥C₀, before the instance; reason: §5.2 fixes A first and then C
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Lemma 5.3, PDF p.21 (printed p.20)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Lemma 5.3 (Row recovery), PDF p.21 (printed p.20). `A`, then `C`, are sufficiently large. -/
theorem lemma_5_3 :
    ∃ A₀ : ℕ, ∀ A ≥ A₀, ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ (n lam N X Y : ℕ),
      let P : HintParams := ⟨A, C, n, lam⟩
      P.NodeArgs N X Y → P.NonLeaf N X Y →
      (∀ (j : Fin (P.rows X Y)) (Jj Sj : Finset ℕ),
        Jj ⊆ range (rowLen N (P.rows X Y) j.val) → Sj ⊆ range (rowLen N (P.rows X Y) j.val) →
        ¬ P.Overloaded N X Y Jj Sj →
        let sch := P.scheme N X Y
        prU (fun β : sch.Rand => sch.final j β Jj (sch.truePrefix j β Sj sch.ℓ) ≠ Sj) ≤
          P.eta ^ 2 / 8) ∧
      (∀ x J : Finset ℕ, Node.Valid N X Y x J →
        expU (fun π : Equiv.Perm (Fin N) => (P.overloadedMass N X Y π x J : ℝ)) ≤
          (HintParams.D N X Y : ℝ) * P.eta ^ 2) := by sorry

end LinearSetReconciliation327.Main
