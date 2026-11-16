-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_lemma_4_6
-- name    : MeanCertificates1424.Hardness.Supplement.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:03:29.175982+00:00
-- url     : https://prove2.me/theorems/c1826b5a-d039-4387-9a37-d444ef9541df
-- title:
--   Lemma 4.6 — linear-time truncated envelopes on a tree
-- statement:
--   Let $T$ be a tree with nonnegative edge lengths, with at most two sources at each vertex, each source having a real initial value and a distinct identity. For $1\le q\le$ the total number of sources, the first $q$ source cones (initial value plus tree distance) at every vertex, ordered by value and then by identity, can be computed in $O(nq)$ arithmetic operations and $O(nq)$ space. In particular, both truncated alphabets $A^\pm_{v,b}$ of Lemma 4.3 can be computed on a tree within these bounds ($q=b+1$).
--
--   This is the preprocessing step of the tree algorithm of Theorem 4.8.
--
--   Differences from the source:
--   - encoding: O(·) arithmetic operations (and space) → one fixed program of the unit-cost real RAM and one constant C>0 chosen before every instance, every executed instruction charged, space = distinct cells accessed; reason: the paper's model counts exact arithmetic operations and comparisons; charging all instructions only strengthens the bound
--   - encoding: both truncated alphabets of Lemma 4.3 → the alphabets with the identity order inl i ↦ i, inr q ↦ n+q; reason: the value sets do not depend on the tie-break order
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Lemma 4.6, printed p.14 (PDF p.16), proof to printed p.15 (PDF p.17)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_RAM

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Lemma 4.6, printed p.14 / PDF p.16 (proof to PDF p.17). One fixed program and constant:
on a tree with nonnegative edge lengths and real-valued sources (location, initial value,
distinct identity; at most two per vertex), for `1 ≤ q ≤` the number of sources, it outputs at
every vertex the first `q` source cones in the order (value, identity) using at most `C n q`
operations and `C n q` cells. In particular one fixed program computes both truncated
alphabets of Lemma 4.3 on a tree within the same bounds (`q = b + 1`). -/
theorem lemma_4_6 :
    (∃ (P : Program) (C : ℕ), 0 < C ∧
      ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (len : Fin n → Fin n → ℝ) (srcs : List (Src n))
        (q : ℕ), T.IsTree → NonnegLengths T len → (srcs.map Src.ident).Nodup →
        (∀ v, (srcs.filter fun s => decide (s.loc = v)).length ≤ 2) →
        1 ≤ q → q ≤ srcs.length →
        ∃ fin, RunsWithin P (fun _ _ => 0) (encAdj T ++ (encSrcs srcs).1 ++ [q])
            (encLengths T len ++ (encSrcs srcs).2) (C * n * q) (C * n * q) fin ∧
          ∀ v, outCones n q fin v = topCones (wdist T len) srcs q v) ∧
    (∃ (P : Program) (C : ℕ), 0 < C ∧
      ∀ I : Inst, Valid I → Anchored I → I.graph.IsTree →
        ∃ fin, RunsWithin P (fun _ _ => 0) (encInst I).1 (encInst I).2
            (C * I.n * (I.budget + 1)) (C * I.n * (I.budget + 1)) fin ∧
          ∀ v, outValues I.n (I.budget + 1) 0 fin v = truncUp I stdOrd v ∧
            outValues I.n (I.budget + 1) I.n fin v = truncLow I stdOrd v) := by sorry

end MeanCertificates1424.Hardness.Supplement
