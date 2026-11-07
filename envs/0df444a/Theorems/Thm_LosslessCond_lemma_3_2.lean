-- Prove2me | Theorems.Thm_LosslessCond_lemma_3_2
-- name    : LosslessCond.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:18.343002+00:00
-- url     : https://prove2.me/theorems/ab7be9a0-5d2c-42e7-ba68-101a7223850c
-- title:
--   Lemma 3.2 — compatibility and protocols: $D(M[U,V])\le s\iff V\subseteq G_P(U)$
-- statement:
--   Let $M:X\times Y\to\{0,1\}$ be a finite Boolean matrix, $s\ge 0$, and $U\subseteq X$ nonempty.
--
--   1. For every nonempty $V\subseteq Y$,
--   $$
--   D(M[U,V])\le s\iff V\subseteq G_P(U)\ \text{for some depth-}s\text{ partial protocol }P.
--   $$
--   2. For every depth-$s$ partial protocol $P$ with $G_P(U)\neq\emptyset$, the whole restriction $M[U,G_P(U)]$ has a protocol of depth at most $s$.
--
--   Here $G_P(U)$ is the protocol domain of Definition 3.1, defined by a single Bob assignment. The lemma turns "every small restriction is cheap" into statements about protocol domains, which can then be counted.
--
--   Differences from the source:
--   - encoding: D(M[U, V]) for the submatrix on U × V → DetCCHard.commCost M U V, the least depth of a protocol on all of X, Y correct on U × V; reason: protocols restrict and extend, so the two costs agree on every instance
--   - encoding: finite nonempty input sets X, Y → finite types X Y : Type (Fintype), nonemptiness not assumed; reason: every finite set is equivalent to a type in universe 0; where nonemptiness matters it is assumed or forced by the other hypotheses
--   - encoding: Alice's message functions specified on U → Alice's message functions on all of X; reason: only their values on U enter the domain G_P(U)
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), Lemma 3.2, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_LosslessCond_domain

namespace LosslessCond

/-- **Lemma 3.2 (Compatibility and protocols)** (Mackenzie, *Lossless Hardness Condensation in
Deterministic Communication Complexity*, arXiv:2609.28691, held version sha256 ce75e6d4…, p.8).
For nonempty `U ⊆ X` and `V ⊆ Y`,
`D(M[U, V]) ≤ s ⟺ V ⊆ G_P(U)` for some depth-`s` partial protocol `P`.
If `G_P(U)` is nonempty, the whole restriction `M[U, G_P(U)]` has a protocol of depth at most `s`.

**Formalization Note** `D(M[U, V])` is `DetCCHard.commCost M U V`; `G_P(U)` is
`LosslessCond.domain M P U`, defined by a single Bob assignment (Definition 3.1). -/
theorem lemma_3_2 {X Y : Type} [Fintype X] [Fintype Y] (M : X → Y → Bool) (s : ℕ)
    (U : Set X) (hU : U.Nonempty) :
    (∀ V : Set Y, V.Nonempty →
      (DetCCHard.commCost M U V ≤ s ↔ ∃ P : PartialProtocol X s, V ⊆ domain M P U)) ∧
    (∀ P : PartialProtocol X s, (domain M P U).Nonempty →
      DetCCHard.commCost M U (domain M P U) ≤ s) := by sorry

end LosslessCond
