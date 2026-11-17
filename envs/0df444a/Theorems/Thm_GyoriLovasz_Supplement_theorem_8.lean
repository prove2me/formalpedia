-- Prove2me | Theorems.Thm_GyoriLovasz_Supplement_theorem_8
-- name    : GyoriLovasz.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:16:05.612498+00:00
-- url     : https://prove2.me/theorems/1725e1b5-d535-4c96-9383-c1ff0440a9a8
-- title:
--   Theorem 8 — incremental extension: grow the part of $t_1$ by one, keep the other part sizes
-- statement:
--   Let $G=(V,E)$ be a directed graph with terminal set $T=\{t_1,\dots,t_k\}\subseteq V$ satisfying the local connectivity condition with respect to capacities $c$. Let $n_1,\dots,n_k$ be integers with $n_i\le c_{t_i}$ for all $i$ and $n_1<c_{t_1}$, and let $V_1,\dots,V_k$ be pairwise disjoint vertex sets with $t_i\in V_i$, $G[V_i]$ connected to $t_i$ and $|V_i\setminus\{t_i\}|=n_i$ for all $i$. Then there are pairwise disjoint vertex sets $V_1',\dots,V_k'$ with $t_i\in V_i'$ and $G[V_i']$ connected to $t_i$ for all $i$, and
--
--   $$
--   |V_1'\setminus\{t_1\}|=n_1+1,\qquad |V_i'\setminus\{t_i\}|=n_i\quad(i\ne 1).
--   $$
--
--   This is the induction step of the proof of Theorem 7: starting from $V_i=\{t_i\}$ and applying it $|V\setminus T|$ times yields the partition. The given sets need not cover $V$, and the new sets need not contain the old ones.
--
--   **Formalization Note** Sets and numbers are indexed by the terminals, and $t_1$ is a distinguished terminal. The graph satisfies the paper's standing assumption of §2.
--
--   Differences from the source:
--   - reading: §2 standing assumption (p.14): no self-loops, terminals have no outgoing edges (WLOG) → hypothesis Std G T; reason: the paper assumes it throughout; it makes 'their terminal endpoints' of Definition A.1 unambiguous
--   - encoding: integers n_1, ..., n_k → n : V → ℕ; reason: |V_i ∖ {t_i}| = n_i forces n_i ≥ 0
--   - encoding: V_1..V_k, n_1..n_k indexed by i ∈ [k], distinguished index 1 → functions on the terminal type, a distinguished t₁ ∈ T; reason: the terminals are distinct, so indexing by i and by t_i agree
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Theorem 8, p.62; Definitions A.1–A.3, pp.54–55

import Mathlib
import Definitions.Def_GyoriLovasz_Std
import Definitions.Def_GyoriLovasz_ConnectedTo
import Definitions.Def_GyoriLovasz_Supplement_LocalCond

namespace GyoriLovasz

namespace Supplement

/-- **Theorem 8 (incremental extension).** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential
Barrier*, arXiv:2608.30945 (held file sha256 3f80f82d…780e), Theorem 8, p.62: "Let G = (V, E) be a directed graph with
terminal set T = {t_1, ..., t_k} ⊆ V that satisfies the local connectivity condition with respect to capacities c. Let
n_1, ..., n_k be integers such that n_i ≤ c_{t_i} for all i ∈ [k] and n_1 < c_{t_1}. Let V_1, ..., V_k be pairwise
disjoint vertex sets such that t_i ∈ V_i, G[V_i] is connected to t_i for all i ∈ [k], and |V_i \ {t_i}| = n_i for all
i ∈ [k]. Then, there exist pairwise disjoint vertex sets V′_1, ..., V′_k such that t_i ∈ V′_i, G[V′_i] is connected to
t_i for all i ∈ [k], |V′_1 \ {t_1}| = n_1 + 1, and |V′_i \ {t_i}| = n_i for all i ∈ [k] \ {1}."

**Formalization Note.** Sets and numbers are indexed by the terminals; `t₁ ∈ T` is the distinguished terminal.
`t ∈ V_t` is a clause of `ConnectedTo`, which also puts every part inside `V`. The given parts need not cover `V`, and
the new parts need not contain the old ones. The `n_i` are natural numbers: the cardinality equation forces the paper's
integers to be nonnegative. `Std G T` is the standing assumption of §2 (p.14). -/
theorem theorem_8 {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) (c : V → ℕ) (t₁ : V)
    (hStd : Std G T) (hT : T ⊆ G.verts) (hloc : LocalCond G T c) (ht₁ : t₁ ∈ T)
    (n : V → ℕ) (hn : ∀ t ∈ T, n t ≤ c t) (hn₁ : n t₁ < c t₁)
    (P : V → Finset V) (hdisj : ∀ s ∈ T, ∀ t ∈ T, s ≠ t → Disjoint (P s) (P t))
    (hconn : ∀ t ∈ T, ConnectedTo G (P t) t) (hcard : ∀ t ∈ T, ((P t).erase t).card = n t) :
    ∃ P' : V → Finset V, (∀ s ∈ T, ∀ t ∈ T, s ≠ t → Disjoint (P' s) (P' t)) ∧
      (∀ t ∈ T, ConnectedTo G (P' t) t) ∧ ((P' t₁).erase t₁).card = n t₁ + 1 ∧
        ∀ t ∈ T, t ≠ t₁ → ((P' t).erase t).card = n t := by sorry

end Supplement

end GyoriLovasz
