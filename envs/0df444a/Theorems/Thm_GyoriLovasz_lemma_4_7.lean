-- Prove2me | Theorems.Thm_GyoriLovasz_lemma_4_7
-- name    : GyoriLovasz.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:52:09.08977+00:00
-- url     : https://prove2.me/theorems/90a1bac5-5584-40d9-9751-956800e84545
-- title:
--   Lemma 4.7 — Hall-deficient terminals are not essential outside their neighbourhood
-- statement:
--   Let $G=(V,E)$ be a directed graph with terminal set $T\subseteq V$, no self-loops and no edge leaving a terminal. Let $S\subseteq T$ be inclusion-minimal subject to $|S|>|\mathrm{PT}(G,S)|$: the inequality holds for $S$ and fails for every proper subset of $S$. Then no terminal $t\in S$ is essential for any non-terminal
--   $$v\in (V\setminus T)\setminus \mathrm{PT}(G,S).$$
--   Equivalently, terminals in $S$ can be essential only for vertices of $\mathrm{PT}(G,S)$.
--
--   The lemma is the core of the proof that a matching from pre-terminals to terminals exists (Lemma 4.8).
--
--   Differences from the source:
--
--   - encoding: the standing assumption of §2, p.14: terminals are vertices, no self-loops or parallel edges, terminals have no outgoing edges (stated once, "without loss of generality") → explicit hypotheses `Std G T` and `T ⊆ G.verts`; parallel edges are impossible in `DG`; reason: trap 19: a section's standing assumption is a hypothesis of each of its results
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Lemma 4.7, p.29

import Mathlib
import Definitions.Def_GyoriLovasz_IsEssential
import Definitions.Def_GyoriLovasz_PT
import Definitions.Def_GyoriLovasz_Std

namespace GyoriLovasz

variable {V : Type*} [DecidableEq V]

/-- **Lemma 4.7 (Hall-deficient terminals are not essential outside their neighborhood).** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Lemma 4.7, p.29: "Let G = (V, E) be a
directed graph with terminal set T. Let S ⊆ T be inclusion-minimal subject to |S| > |PT(G, S)|. Then no terminal t ∈ S is essential for any
non-terminal vertex v ∈ (V \ T) \ PT(G, S). Equivalently, terminals in S can be essential only for vertices in PT(G, S)."

**Formalization Note.** Inclusion-minimal is the condition on `S` and its failure on every proper subset. The empty set never
satisfies the condition. `Std` and `T ⊆ V` are the standing assumptions of §2. -/
theorem lemma_4_7 (G : DG V) (T S : Finset V) (hstd : Std G T) (hT : T ⊆ G.verts) (hST : S ⊆ T)
    (hS : (PT G T S).card < S.card) (hmin : ∀ S' ⊂ S, ¬ (PT G T S').card < S'.card) :
    ∀ t ∈ S, ∀ v ∈ (G.verts \ T) \ PT G T S, ¬ IsEssential G T v t := by sorry

end GyoriLovasz
