-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_lemma_6_2
-- name    : LinearSetReconciliation327.Main.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:22.287205+00:00
-- url     : https://prove2.me/theorems/b0e412ee-c97c-4545-a35b-087f64073acd
-- title:
--   Lemma 6.2 — Within a word
-- statement:
--   With $p_k=2^{w-k}/(2^w-1)$: for each row and word, the joint event identity $\Pr[\text{word prediction incorrect and first incorrect bit is }k]=p_k\Pr[\text{word prediction incorrect}]$ holds, $\sum_{k=1}^wp_k=1$, $H((p_k)_{k=1}^w)\le2$, and for every $x\in S_{n,d}$ and column $(a,k)$, $\mathbb EV_{a,k}\le q_ap_k$.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
--   - encoding: Pr and E over the node randomness → uniform averages over the finite type of a permutation of [N] and the row coins; reason: this is the source law; coins for indices up to N_max beyond a shorter row are never read
--   - encoding: conditional on a row’s word prediction being incorrect → joint-event identity Pr[E and F] = p_k Pr[E]; reason: it is the conditional law where defined and is meaningful when the event has probability zero
--   - generalization: stated in the row-column regime of §6.2 → all 2 ≤ d ≤ n and every value of C′; reason: the source proof uses only the scalar and Pinsketch; the regime is a special case
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Lemma 6.2, PDF p.29 (printed p.28)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_TopLevel

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

open Classical in
/-- Lemma 6.2 (Within a word), PDF p.29 (printed p.28). Conditioning is written as a joint-event
identity, since the conditioning event may have probability zero. `u` is the unscaled prediction from
the candidate of the exact prefix, `v` the true value; source indices `a, k` are `a + 1, k + 1`. -/
theorem lemma_6_2 (P : TopParams) (hargs : P.Args) (F : Type) [Field F] [Fintype F]
    [Algebra (ZMod 2) F] (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (hι : P.IsAddress ι)
    (x : Finset ℕ) (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) :
    let sch := P.scheme b ι
    let cands : sch.LocalSeed → Fin P.d → Fin P.B → Option (Finset ℕ) := fun lr j a =>
      P.cand b ι j.val (lr.2 j)
        (sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) (a.val * P.w)) a.val
    let wrongWord : sch.LocalSeed → Fin P.d → Fin P.B → Prop := fun lr j a =>
      ∃ C, cands lr j a = some C ∧
        TopParams.power ι (2 * a.val + 1) C ≠
          TopParams.power ι (2 * a.val + 1) (sch.rowOf lr x j)
    (∀ (j : Fin P.d) (a : Fin P.B) (k : Fin P.w),
      prU (fun lr : sch.LocalSeed => wrongWord lr j a ∧ ∃ C, cands lr j a = some C ∧
          let α : F := ((lr.2 j : Fin P.B → Fˣ) a : F)
          let bu := b.repr (α * TopParams.power ι (2 * a.val + 1) C)
          let bv := b.repr (α * TopParams.power ι (2 * a.val + 1) (sch.rowOf lr x j))
          (∀ k' : Fin P.w, k'.val < k.val → bu k' = bv k') ∧ bu k ≠ bv k) =
        P.p k.val * prU (fun lr : sch.LocalSeed => wrongWord lr j a)) ∧
    (∑ k ∈ range P.w, P.p k = 1) ∧
    entropyFin (fun k : Fin P.w => P.p k.val) ≤ 2 ∧
    (∀ s : Fin P.ell,
      expU (fun lr : sch.LocalSeed => (sch.V lr x ∅ s : ℝ)) ≤
        P.q ((P.wordIdx s).val + 1) * P.p (P.bitIdx s).val) := by sorry

end LinearSetReconciliation327.Main
