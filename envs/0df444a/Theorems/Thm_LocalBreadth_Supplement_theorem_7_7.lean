-- Prove2me | Theorems.Thm_LocalBreadth_Supplement_theorem_7_7
-- name    : LocalBreadth.Supplement.theorem_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:27:02.429772+00:00
-- url     : https://prove2.me/theorems/61853260-5cd7-403e-bb1e-f0cfd78285ae
-- title:
--   Theorem 7.7 — topological characterization of $q$-protected trees
-- statement:
--   Throughout, as in all of §7, $d\ge2$, $\mathcal X$ is a nonempty countable family of infinite subsets of $\mathbb Z^d$, and the threshold is $h(V)=u(V)\log(2+V)$ with $u:[1,\infty)\to(0,\infty)$ nondecreasing.
--
--   Let $q:\mathcal X\to[0,1]$ be a quota profile and $K\in\mathcal X$. A $q$-protected tree rooted at $K$ exists if and only if the one-language history $(K)$ has an open neighborhood $\mathcal U\subseteq\mathcal H_K$ in the finite-evidence history topology, closed under taking prefixes, that admits a $q$-good geometric decoration (Definition 7.6).
--
--   This identifies the combinatorial certificates of §7 with decorated open neighborhoods, the same unfolding that relates obstruction trees to the history topology in dimension one.
--
--   Differences from the source:
--   - encoding: h(V) = u(V) log(2+V), u : [1, ∞) → (0, ∞) nondecreasing → IsLogThreshold h: ∃ u : ℝ → ℝ positive and monotone on [1, ∞) with h V = u V · log(2 + V) for V ≥ 1; reason: same class; values of u below 1 and of h at 0 are never used
--   - encoding: profile q : X → [0, 1] → q : Set (Fin d → ℤ) → ℝ with 0 ≤ q L ≤ 1 for L ∈ X; reason: values off X are never used
--   - encoding: countable rooted tree with vertex labels → DecoratedTree: vertices are a prefix-closed set of finite sequences of naturals (root []), children v ++ [n]; reason: every countable rooted tree is isomorphic to one of this form, and every such tree is countable
--   - reading: (K) has an open neighborhood in ℋ_K that admits a q-good geometric decoration → ∃ U open in the history topology, U ⊆ ℋ_K, (K) ∈ U, U prefix-closed, with a q-good decoration; reason: Definition 7.6 defines decorations only for open neighborhoods of (K) in ℋ_K closed under taking prefixes
--   - encoding: cutoff s_H and radius a_H assigned to each history H ∈ U → functions s, a : List (Set (Fin d → ℤ)) → ℝ evaluated at the chain of H; reason: a history is determined by its chain; only values on histories in U are used
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc309339291b1a61b8504342f4050ece6e4e903dd18b2bf541446f1064), §7.3.1, Theorem 7.7, p.58 (PDF p.60); Definition 7.6, p.58

import Mathlib
import Definitions.Def_LocalBreadth_Supplement_IsProtectedTree
import Definitions.Def_LocalBreadth_Supplement_IsGoodDecoration

open scoped Topology

namespace LocalBreadth.Supplement

/-- Theorem 7.7 (topological characterization). Kleinberg, Wei, STOC 2027 submission (manuscript
sha256 f924cbfc…), §7.3.1, p.58. Under the standing assumptions of §7, for a quota profile
`q : X → [0, 1]` and `K ∈ X`: a `q`-protected tree rooted at `K` exists if and only if `(K)` has an
open neighborhood in `ℋ_K`, closed under taking prefixes, that admits a `q`-good geometric decoration.

**Formalization Note.** "Open neighborhood in `ℋ_K`" is an open set of the finite-evidence history
topology contained in `ℋ_K` and containing the one-language history `(K)`; prefix-closedness is part
of Definition 7.6, which defines decorations only for such sets. -/
theorem theorem_7_7 (d : ℕ) (hd : 2 ≤ d) (X : Set (Set (Fin d → ℤ))) (hne : X.Nonempty)
    (hc : X.Countable) (hinf : ∀ L ∈ X, L.Infinite) (h : ℕ → ℝ) (hh : IsLogThreshold h)
    (q : Set (Fin d → ℤ) → ℝ) (hq : ∀ L ∈ X, 0 ≤ q L ∧ q L ≤ 1) (K : Set (Fin d → ℤ))
    (hK : K ∈ X) :
    (∃ T, IsProtectedTree h q X K T) ↔
      ∃ U : Set (HistoryP (Fin d → ℤ) X), IsOpen[historyTopologyP X] U ∧
        U ⊆ historiesFromP X K ∧ (∃ H ∈ U, H.chain = [K]) ∧ IsPrefixClosed U ∧
        ∃ s a : List (Set (Fin d → ℤ)) → ℝ, IsGoodDecoration h q U s a := by sorry

end LocalBreadth.Supplement
