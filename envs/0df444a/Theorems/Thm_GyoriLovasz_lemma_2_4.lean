-- Prove2me | Theorems.Thm_GyoriLovasz_lemma_2_4
-- name    : GyoriLovasz.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:51:38.62045+00:00
-- url     : https://prove2.me/theorems/6830b4d6-c455-4612-b848-f460e90ebbcb
-- title:
--   Lemma 2.4 — directed Menger theorem for terminal connectivity
-- statement:
--   Let $G=(V,E)$ be a directed graph with terminal set $T\subseteq V$, no self-loops, and no edge leaving a terminal, and let $v\in V\setminus T$. Then the maximum number of vertex-disjoint paths from $v$ to distinct terminals equals the minimum size of a cut separating $v$ from $T$:
--   $$\kappa_G(v)=\min\{|S_C| : C=(L_C,S_C,R_C)\text{ separates } v \text{ from } T\}.$$
--
--   That is, some cut separating $v$ from $T$ has size $\kappa_G(v)$, and every such cut has size at least $\kappa_G(v)$.
--
--   This is the directed, vertex form of Menger's theorem with a common start vertex and a set of targets. It underlies every cut argument of the paper.
--
--   Differences from the source:
--
--   - encoding: κ_G(v) = min{|S_C| : C separates v from T} → a cut with |S| = κ_G(v) exists and every cut has |S| ≥ κ_G(v); reason: the two clauses are the definition of a minimum
--   - encoding: the standing assumption of §2, p.14: terminals are vertices, no self-loops or parallel edges, terminals have no outgoing edges (stated once, "without loss of generality") → explicit hypotheses `Std G T` and `T ⊆ G.verts`; parallel edges are impossible in `DG`; reason: trap 19: a section's standing assumption is a hypothesis of each of its results
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Lemma 2.4, p.15

import Mathlib
import Definitions.Def_GyoriLovasz_kappa
import Definitions.Def_GyoriLovasz_IsCut
import Definitions.Def_GyoriLovasz_Std

namespace GyoriLovasz

variable {V : Type*} [DecidableEq V]

/-- **Lemma 2.4 (Menger's theorem).** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Lemma 2.4, p.15: "For every non-terminal vertex v ∈ V \ T, the maximum
number of vertex-disjoint paths from v to distinct terminals equals the minimum size of a cut separating v from T. That
is, κ_G(v) = min{|S_C| : C = (L_C, S_C, R_C) separates v from T}."

**Formalization Note.** The minimum is stated as: a cut of size `κ_G(v)` exists, and every cut has size at least
`κ_G(v)`. This is the directed vertex form with a common start and a set of targets. `Std` and `T ⊆ V` are the standing
assumptions of §2, p.14. -/
theorem lemma_2_4 (G : DG V) (T : Finset V) (v : V) (hstd : Std G T) (hT : T ⊆ G.verts)
    (hv : v ∈ G.verts \ T) :
    (∃ L S R, IsCut G T v L S R ∧ S.card = kappa G T v) ∧
      ∀ L S R, IsCut G T v L S R → kappa G T v ≤ S.card := by sorry

end GyoriLovasz
