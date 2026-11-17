-- Prove2me | Theorems.Thm_GyoriLovasz_Supplement_theorem_7
-- name    : GyoriLovasz.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:15:28.073211+00:00
-- url     : https://prove2.me/theorems/bea0f140-43d9-47b1-a538-453632c9bebe
-- title:
--   Theorem 7 — the Győri–Lovász theorem under local connectivity
-- statement:
--   Let $G=(V,E)$ be a directed graph with terminal set $T=\{t_1,\dots,t_k\}\subseteq V$ and capacities $c_t\in\mathbb N$ with
--
--   $$
--   \sum_{t\in T}c_t=|V\setminus T| .
--   $$
--
--   If $G$ satisfies the **local connectivity condition** with respect to $T$ and $c$ (for every $T'\subseteq T$, at least $\sum_{t\in T'}c_t$ non-terminals have $|T'|$ internally vertex-disjoint paths to $T'$ or are pre-terminals of some $t\in T'$), then there is a partition $\langle V_i\rangle_{i\in[k]}$ of $V$ such that for every $i$
--
--   $$
--   t_i\in V_i,\qquad |V_i\setminus\{t_i\}|=c_{t_i},\qquad G[V_i]\text{ is connected to }t_i .
--   $$
--
--   Local connectivity is implied by $k$-$T$-connectivity (Lemma A.4), so this extends the existence part of the Győri–Lovász theorem to a weaker connectivity hypothesis. It is a pure existence statement; no running time is claimed.
--
--   **Formalization Note** The parts are indexed by the terminals; $|V_t|=c_t+1$ in the base definition `IsGLPartition` is $|V_t\setminus\{t\}|=c_t$ because $t\in V_t$. The graph satisfies the paper's standing assumption of §2 (no self-loops, terminals have no outgoing edges).
--
--   Differences from the source:
--   - reading: §2 standing assumption (p.14): no self-loops, terminals have no outgoing edges (WLOG) → hypothesis Std G T; reason: the paper assumes it throughout; it makes 'their terminal endpoints' of Definition A.1 unambiguous
--   - encoding: partition ⟨V_i⟩_{i∈[k]} with |V_i ∖ {t_i}| = c_{t_i} → IsGLPartition G T c parts, parts indexed by terminals, |parts t| = c t + 1; reason: t ∈ parts t, so the two cardinalities agree
--   - encoding: T = {t_1, ..., t_k} ⊆ V → T : Finset V with T ⊆ G.verts; reason: same data
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Theorem 7, p.55; Definitions A.1–A.3, pp.54–55

import Mathlib
import Definitions.Def_GyoriLovasz_Std
import Definitions.Def_GyoriLovasz_IsGLPartition
import Definitions.Def_GyoriLovasz_Supplement_LocalCond

namespace GyoriLovasz

namespace Supplement

/-- **Theorem 7 (the Győri–Lovász theorem under local connectivity).** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani,
*Breaking the Exponential Barrier*, arXiv:2608.30945 (held file sha256 3f80f82d…780e), Theorem 7, p.55: "Let
G = (V, E) be a directed graph with terminal set T = {t_1, ..., t_k} ⊆ V, and let c_t ∈ ℕ for all t ∈ T. Assume that
∑_{t∈T} c_t = |V \ T|. If G satisfies the local connectivity condition with respect to T and c, then there exists a
partition ⟨V_i⟩_{i∈[k]} of V such that, for every i ∈ [k], we have t_i ∈ V_i, |V_i \ {t_i}| = c_{t_i}, and G[V_i] is
connected to t_i."

**Formalization Note.** A pure existence statement. Parts are indexed by the terminals (`IsGLPartition`, published);
`|V_i| = c_{t_i} + 1` there is `|V_i \ {t_i}| = c_{t_i}` because `t_i ∈ V_i`. `Std G T` is the paper's standing
assumption of §2 (p.14: no self-loops, terminals have no outgoing edges), under which the internally vertex-disjoint
paths of Definition A.1 are unambiguous. -/
theorem theorem_7 {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) (c : V → ℕ)
    (hStd : Std G T) (hT : T ⊆ G.verts) (hsum : ∑ t ∈ T, c t = (G.verts \ T).card)
    (hloc : LocalCond G T c) :
    ∃ parts : V → Finset V, IsGLPartition G T c parts := by sorry

end Supplement

end GyoriLovasz
