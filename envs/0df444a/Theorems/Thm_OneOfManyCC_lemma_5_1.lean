-- Prove2me | Theorems.Thm_OneOfManyCC_lemma_5_1
-- name    : OneOfManyCC.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:54.790313+00:00
-- url     : https://prove2.me/theorems/161028b2-ce04-42a6-b35e-a3a9d7eb0bd9
-- title:
--   Lemma 5.1 (Zermelo) — exactly one of: Alice forces $L$, Bob forces the complement of $L$
-- statement:
--   Let $P$ be a protocol tree and $L$ a set of leaves of $P$. Then exactly one of the following holds:
--
--   1. Alice can force $L$;
--   2. Bob can force the complement of $L$ in the set of leaves of $P$.
--
--   This is the determinacy of the finite game on the tree. It converts "Alice cannot force" into "Bob can force the complement" in the proof of Lemma 5.2.
--
--   **Formalization Note** The complement is taken in the leaves of $P$, since paths that are not leaves are also elements of `List Bool`.
--
--   Differences from the source:
--   - generalization: $P$ is the fixed optimal protocol for $\mathrm{OneOut}^{\neq}_k(R)$ → any protocol tree on any sets $A,B,O$; reason: the game depends only on the tree shape; the paper's $P$ is one such tree
--   - encoding: a node or leaf of $P$ → its path `List Bool` from the root; reason: leaves with equal labels stay different leaves
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), Lemma 5.1, p.10

import Mathlib
import Definitions.Def_OneOfManyCC_LeafSets
import Definitions.Def_OneOfManyCC_Forcing

namespace OneOfManyCC

/-- **Lemma 5.1 (Zermelo).**
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), Lemma 5.1, p.10:
"For every set L of leaves of P, either Alice can force L or Bob can force the complement of L, but
not both."

**Formalization Note.** Stated for every protocol tree; the paper's `P` is a fixed optimal protocol
for `OneOut≠ₖ(R)`, whose properties the lemma does not use. The complement is taken in the set of
leaves of `P`. `Xor'` is "exactly one of the two". -/
theorem lemma_5_1 {A B O : Type} (P : Protocol A B O) (L : Set (List Bool)) (hL : L ⊆ P.leaves) :
    Xor' (P.AliceForces L) (P.BobForces (P.leaves \ L)) := by sorry

end OneOfManyCC
