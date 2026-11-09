-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_lemma_6_4
-- name    : LinearSetReconciliation327.Main.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:25.697202+00:00
-- url     : https://prove2.me/theorems/791514ad-59fa-4977-84a1-e8609d9b9d26
-- title:
--   Lemma 6.4 — Top-layer residual repair
-- statement:
--   Fix $A\ge10$ and a CR family with $\mathrm{rows}\le K_{CR}t\log^2(N+2)$. There is $K$ such that for sufficiently large $C'$, in the row-column regime, for $t=\min\{n,d(B+1),\lceil2\eta(d+1)\rceil\}$ and every $x\in S_{n,d}$: $\Pr[Z>t]\le2^{-\lambda_*}$, and the final CR sketch has at most $Kd/\log n$ rows.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
--   - encoding: Pr and E over the node randomness → uniform averages over the finite type of a permutation of [N] and the row coins; reason: this is the source law; coins for indices up to N_max beyond a shorter row are never read
--   - encoding: the CR sketch of Proposition 2.3 → rows of any CR family with the row bound of Proposition 2.3; reason: the source proof uses only this row bound
--   - encoding: A fixed in §5 with A ≥ 10 w.l.o.g. (Lemma 6.3) → hypothesis A ≥ 10; reason: the choice made in the proof of Lemma 6.3
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Lemma 6.4, PDF p.30 (printed p.29)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_TopLevel

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Lemma 6.4 (Residual repair), PDF p.30 (printed p.29). `A` is the fixed constant of §5, the CR
family has the row bound of Proposition 2.3, and `C'` is sufficiently large. -/
theorem lemma_6_4 (A : ℕ) (hA : 10 ≤ A) (KCR : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ C₀ : ℕ, ∀ C' ≥ C₀, ∀ (n d lam : ℕ) (CR : CRFamily),
      (∀ N' t : ℕ, t ≤ N' → (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2)) →
      let P : TopParams := ⟨A, C', n, d, lam⟩
      P.Args → P.RowColumnRegime →
      ∀ (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
        (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F), P.IsAddress ι →
      (∀ x : Finset ℕ, x ⊆ range P.n → x.card ≤ P.d →
        let sch := P.scheme b ι
        prU (fun lr : sch.LocalSeed => P.resid < sch.Z lr x ∅) ≤ ((2 : ℝ) ^ P.lamStar)⁻¹) ∧
      (CR.rows n P.resid : ℝ) ≤ K * ((d : ℝ) / P.lgn) := by sorry

end LinearSetReconciliation327.Main
