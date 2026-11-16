-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_lemma_4_5
-- name    : MeanCertificates1424.Hardness.Supplement.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:05:32.804197+00:00
-- url     : https://prove2.me/theorems/62c29214-1a92-4e22-9c67-5e3b42743aa5
-- title:
--   Lemma 4.5 — computing the truncated alphabets on graphs
-- statement:
--   Let $q=b+1$ and $X=(n+|E|)q$. Both truncated alphabet families $A^\pm_{v,b}$ can be computed on a connected graph in
--   $$O\big(X\log(X+1)\big)$$
--   arithmetic operations and $O(X)$ space, without all-pairs distances. The same bound holds for nonnegative edge lengths, where the cones use $L\,d_{\mathrm{len}}$.
--
--   This is the preprocessing step of the bounded-treewidth algorithm of Theorem 5.2.
--
--   Differences from the source:
--   - encoding: O(·) arithmetic operations (and space) → one fixed program of the unit-cost real RAM and one constant C>0 chosen before every instance, every executed instruction charged, space = distinct cells accessed; reason: the paper's model counts exact arithmetic operations and comparisons; charging all instructions only strengthens the bound
--   - encoding: both truncated alphabet families → the alphabets with the identity order inl i ↦ i, inr q ↦ n+q; reason: the value sets do not depend on the tie-break order
--   - reading: without all-pairs distances → only the operation and space bounds are stated; reason: the phrase describes the method; the stated bounds are the formal content
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Lemma 4.5, printed p.14 (PDF p.16); edge lengths per Remark 6.5, printed p.21 (PDF p.23)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_RAM

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Lemma 4.5, printed p.14 / PDF p.16. With `q = b + 1` and `X = (n + |E|) q`, one fixed
program computes both truncated alphabet families on every connected graph within
`C X log(X + 1)` operations and `C X` cells (no all-pairs distances); the same holds with
nonnegative edge lengths (cones `L · d_len`, Remark 6.5). -/
theorem lemma_4_5 :
    (∃ (P : Program) (C : ℕ), 0 < C ∧
      ∀ I : Inst, Valid I → Anchored I →
        ∃ fin, RunsWithin P (fun _ _ => 0) (encInst I).1 (encInst I).2
            ⌊(C : ℝ) * ((I.n + numEdges I.graph) * (I.budget + 1) : ℕ) *
              Real.log (((I.n + numEdges I.graph) * (I.budget + 1) : ℕ) + 1)⌋₊
            (C * ((I.n + numEdges I.graph) * (I.budget + 1))) fin ∧
          ∀ v, outValues I.n (I.budget + 1) 0 fin v = truncUp I stdOrd v ∧
            outValues I.n (I.budget + 1) I.n fin v = truncLow I stdOrd v) ∧
    (∃ (P : Program) (C : ℕ), 0 < C ∧
      ∀ (I : Inst) (len : Fin I.n → Fin I.n → ℝ), Valid I → Anchored I →
        NonnegLengths I.graph len →
        ∃ fin, RunsWithin P (fun _ _ => 0) (encInst I).1 ((encInst I).2 ++ encLengths I.graph len)
            ⌊(C : ℝ) * ((I.n + numEdges I.graph) * (I.budget + 1) : ℕ) *
              Real.log (((I.n + numEdges I.graph) * (I.budget + 1) : ℕ) + 1)⌋₊
            (C * ((I.n + numEdges I.graph) * (I.budget + 1))) fin ∧
          ∀ v, outValues I.n (I.budget + 1) 0 fin v =
              truncUpD I (fun u v => I.lip * wdist I.graph len u v) stdOrd v ∧
            outValues I.n (I.budget + 1) I.n fin v =
              truncLowD I (fun u v => I.lip * wdist I.graph len u v) stdOrd v) := by sorry

end MeanCertificates1424.Hardness.Supplement
