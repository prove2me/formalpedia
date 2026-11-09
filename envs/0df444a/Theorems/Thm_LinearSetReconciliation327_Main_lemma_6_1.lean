-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_lemma_6_1
-- name    : LinearSetReconciliation327.Main.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:42.567601+00:00
-- url     : https://prove2.me/theorems/77fa3eb0-bfeb-41b9-b90a-2473ab17c681
-- title:
--   Lemma 6.1 — Across words
-- statement:
--   Place $d$ reference labels uniformly at distinct positions of $[n]$, let $T_j$ count those in row $j$, and $q_a=\sum_j\Pr[T_j\ge a]$ for $a\ge1$. For every $x\in S_{n,d}$ and column $(a,k)$: $\mathbb EU_{a,k}\le q_a$, $\sum_{a\ge1}q_a=d$, and $H((q_a/d)_{a\ge1})\le\log(2e)$.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
--   - encoding: Pr and E over the node randomness → uniform averages over the finite type of a permutation of [N] and the row coins; reason: this is the source law; coins for indices up to N_max beyond a shorter row are never read
--   - generalization: stated in the row-column regime of §6.2 → all 2 ≤ d ≤ n and every value of C′; reason: the source proof uses only d ≤ n and the Pinsketch uniqueness; the regime is a special case
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Lemma 6.1, PDF p.28 (printed p.27)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_TopLevel

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Lemma 6.1 (Across words), PDF p.28 (printed p.27). Source word `a` is `a + 1` here. -/
theorem lemma_6_1 (P : TopParams) (hargs : P.Args) (F : Type) [Field F] [Fintype F]
    [Algebra (ZMod 2) F] (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (hι : P.IsAddress ι)
    (x : Finset ℕ) (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) :
    (∀ s : Fin P.ell,
      expU (fun lr : (P.scheme b ι).LocalSeed => ((P.scheme b ι).U lr x ∅ s : ℝ)) ≤
        P.q ((P.wordIdx s).val + 1)) ∧
    (∑' a : ℕ, ENNReal.ofReal (P.q (a + 1))) = (P.d : ℝ≥0∞) ∧
    entropy (fun a : ℕ => P.q (a + 1) / (P.d : ℝ)) ≤
      ENNReal.ofReal (lg (2 * Real.exp 1)) := by sorry

end LinearSetReconciliation327.Main
