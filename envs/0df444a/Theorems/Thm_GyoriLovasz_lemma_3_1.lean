-- Prove2me | Theorems.Thm_GyoriLovasz_lemma_3_1
-- name    : GyoriLovasz.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:52:19.305193+00:00
-- url     : https://prove2.me/theorems/13f596bd-d29f-4a8b-a53b-727a0692868a
-- title:
--   Lemma 3.1 — essential terminals are the terminals in the tightest minimum cut
-- statement:
--   Let $G=(V,E)$ be a directed graph with terminal set $T\subseteq V$, no self-loops and no edge leaving a terminal, and let $v\in V\setminus T$. The tightest minimum cut $C=(L_C,S_C,R_C)$ separating $v$ from $T$ exists, and for it, a terminal $t\in T$ is essential for $v$ if and only if
--   $$t\in S_C.$$
--
--   The lemma turns essentiality, a statement about $|T|+1$ connectivity values, into membership in one canonical cut. It is used whenever terminals are deleted or critical edges are compared.
--
--   Differences from the source:
--
--   - reading: "let C be the tightest minimum cut" (its existence is asserted after Definition 2.8, p.17, by Corollary 2.7) → a first clause asserting that a tightest minimum cut exists, and the equivalence for every (L, S, R) satisfying IsTightest; reason: the definite article presupposes existence; the predicate determines the cut, so 'every' and 'the' agree
--   - encoding: the standing assumption of §2, p.14: terminals are vertices, no self-loops or parallel edges, terminals have no outgoing edges (stated once, "without loss of generality") → explicit hypotheses `Std G T` and `T ⊆ G.verts`; parallel edges are impossible in `DG`; reason: trap 19: a section's standing assumption is a hypothesis of each of its results
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Lemma 3.1, p.17

import Mathlib
import Definitions.Def_GyoriLovasz_IsEssential
import Definitions.Def_GyoriLovasz_IsCut
import Definitions.Def_GyoriLovasz_Std

namespace GyoriLovasz

variable {V : Type*} [DecidableEq V]

/-- **Lemma 3.1.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Lemma 3.1, p.17: "Let G = (V, E) be a directed graph with terminal set T, let v ∈ V \ T, and let
C = (L_C, S_C, R_C) be the tightest minimum cut separating v from T in G. A terminal t ∈ T is essential for v in G if and
only if t ∈ S_C."

**Formalization Note.** Definition 2.8 presupposes that the tightest minimum cut exists (p.17, by Corollary 2.7), so this
is the first clause. `IsTightest` determines the cut. `Std` and `T ⊆ V` are the standing assumptions of §2. -/
theorem lemma_3_1 (G : DG V) (T : Finset V) (v : V) (hstd : Std G T) (hT : T ⊆ G.verts)
    (hv : v ∈ G.verts \ T) :
    (∃ L S R, IsTightest G T v L S R) ∧
      ∀ L S R, IsTightest G T v L S R → ∀ t ∈ T, (IsEssential G T v t ↔ t ∈ S) := by sorry

end GyoriLovasz
