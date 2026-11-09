-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_lemma_6_3
-- name    : LinearSetReconciliation327.Main.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:23.950542+00:00
-- url     : https://prove2.me/theorems/301deaf8-ff0a-42b0-bd96-026f2b965ade
-- title:
--   Lemma 6.3 — Top-layer child capacities
-- statement:
--   Fix $A\ge10$ and $\alpha\ge0$. There is $K$ such that for sufficiently large $C'$, in the row-column regime, for every $x\in S_{n,d}$ each of $U_{a,k}>X_{a,k}$, $V_{a,k}>Y_{a,k}$ has probability at most $2^{-\lambda_*}$, and $\sum_{a,k}X_{a,k}\le dw+KC'd/\log n$, $\sum_{a,k}h_d(Y_{a,k})\le Kd+KC'd/\log n$, $\sum_{a,k}(X_{a,k}+\alpha h_d(Y_{a,k}))\le dw+Kd+KC'd/\log n$.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
--   - encoding: Pr and E over the node randomness → uniform averages over the finite type of a permutation of [N] and the row coins; reason: this is the source law; coins for indices up to N_max beyond a shorter row are never read
--   - encoding: O(d) + O(C′d/log n), with A, α fixed in §6.2 → K independent of C′, chosen after A and α; reason: the source treats A and α as absolute constants of §5
--   - encoding: w.l.o.g. A ≥ 10 → hypothesis A ≥ 10; reason: the source proof assumes it explicitly
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Lemma 6.3, PDF p.30 (printed p.29)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_TopLevel

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Lemma 6.3 (Top-layer child capacities), PDF p.30 (printed p.29). `A` and `α` are the fixed
constants of §5; the hidden constant `K` precedes `C'`, which is sufficiently large. -/
theorem lemma_6_3 (A : ℕ) (hA : 10 ≤ A) (α : ℝ) (hα : 0 ≤ α) :
    ∃ K : ℝ, 0 < K ∧ ∃ C₀ : ℕ, ∀ C' ≥ C₀, ∀ (n d lam : ℕ),
      let P : TopParams := ⟨A, C', n, d, lam⟩
      P.Args → P.RowColumnRegime →
      ∀ (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
        (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F), P.IsAddress ι →
      (∀ x : Finset ℕ, x ⊆ range P.n → x.card ≤ P.d →
        let sch := P.scheme b ι
        ∀ s : Fin P.ell,
          prU (fun lr : sch.LocalSeed => P.capX (P.wordIdx s).val < sch.U lr x ∅ s) ≤
            ((2 : ℝ) ^ P.lamStar)⁻¹ ∧
          prU (fun lr : sch.LocalSeed =>
              P.capY (P.wordIdx s).val (P.bitIdx s).val < sch.V lr x ∅ s) ≤
            ((2 : ℝ) ^ P.lamStar)⁻¹) ∧
      (∑ a ∈ range P.B, ∑ _k ∈ range P.w, (P.capX a : ℝ) ≤
        (d : ℝ) * P.w + K * ((C' : ℝ) * d / P.lgn)) ∧
      (∑ a ∈ range P.B, ∑ k ∈ range P.w, hN d (P.capY a k) ≤
        K * d + K * ((C' : ℝ) * d / P.lgn)) ∧
      (∑ a ∈ range P.B, ∑ k ∈ range P.w, ((P.capX a : ℝ) + α * hN d (P.capY a k)) ≤
        (d : ℝ) * P.w + K * d + K * ((C' : ℝ) * d / P.lgn)) := by sorry

end LinearSetReconciliation327.Main
