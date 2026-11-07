-- Prove2me | Theorems.Thm_MatroidSensOracle_theorem_2_12
-- name    : MatroidSensOracle.theorem_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:01.930074+00:00
-- url     : https://prove2.me/theorems/323bfe07-2b42-4913-9cae-f8517a9dbcaf
-- title:
--   Theorem 2.12 (Davies–McDiarmid): for SBO matroids, $k$ common independent sets iff $k$ independent sets in each
-- statement:
--   Let $M_1$ and $M_2$ be strongly base-orderable matroids on the same finite ground set $E$, let $k\ge0$ and $S\subseteq E$. Then $S$ can be partitioned into $k$ sets that are independent in both $M_1$ and $M_2$ if and only if $S$ can be partitioned into $k$ independent sets of $M_1$ and into $k$ independent sets of $M_2$.
--
--   Lemma 5.1 uses it for the partition matroids $M_{\mathrm{out}}$, $M_{\mathrm{in}}$, which are strongly base-orderable.
--
--   Differences from the source:
--   - encoding: matroids with a finite ground set; partitions into k sets → Mathlib matroids with M₁ finite and M₁.E = M₂.E; parts may be empty; reason: the empty set is independent, so empty parts are the usual convention
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 2.12, p.14 (PDF p.17), citing Davies and McDiarmid [33]

import Mathlib
import Definitions.Def_MatroidSensOracle_LinearMatroid

set_option autoImplicit false

namespace MatroidSensOracle

/-- **Theorem 2.12 (Davies–McDiarmid [33]).** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version,
sha256 0de50841…), p.14 (PDF p.17): "Let M1 and M2 be strongly base-orderable matroids on the same
ground set E. Then for any S ⊆ E, S can be partitioned into k common independent sets of M1 and M2 if
and only if S can be partitioned into k independent sets of M1 and into k independent sets of M2."

**Formalization Note.** Mathlib matroids with a finite ground set (Definition 2.7: "a finite ground set
E"); `IsSBO` is Definition 2.11. A partition into `k` sets allows empty parts. -/
theorem theorem_2_12 {α : Type*} (M₁ M₂ : Matroid α) [M₁.Finite] (hE : M₁.E = M₂.E)
    (h₁ : IsSBO M₁) (h₂ : IsSBO M₂) (k : ℕ) (S : Set α) (hS : S ⊆ M₁.E) :
    SetPartitionsInto (fun X => M₁.Indep X ∧ M₂.Indep X) k S ↔
      SetPartitionsInto M₁.Indep k S ∧ SetPartitionsInto M₂.Indep k S := by sorry

end MatroidSensOracle
