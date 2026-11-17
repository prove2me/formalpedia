-- Prove2me | Theorems.Thm_LocalBreadth_Supplement_theorem_7_2
-- name    : LocalBreadth.Supplement.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:26:33.23133+00:00
-- url     : https://prove2.me/theorems/e9c8ddbe-8041-44c4-b564-6e2203e27211
-- title:
--   Theorem 7.2 — exact simultaneous profile characterization
-- statement:
--   Throughout, as in all of §7, $d\ge2$, $\mathcal X$ is a nonempty countable family of infinite subsets of $\mathbb Z^d$, and the threshold is $h(V)=u(V)\log(2+V)$ with $u:[1,\infty)\to(0,\infty)$ nondecreasing.
--
--   A profile $\alpha:\mathcal X\to[0,1]$ is achieved by one globally fresh, universally eventually valid generator, i.e. $\delta_h(O,K)\ge\alpha(K)$ for every $K\in\mathcal X$ and every full enumeration of $K$, if and only if every accuracy copy $(K,k)$, $K\in\mathcal X$, $k\ge1$, has a protected tree on copies in the sense of Definition 7.14 (quota $q(L,k)=(\alpha(L)-2^{-k})_+$).
--
--   Every local condition of this criterion is finite: a finite history, a finite protected set and a finite stopping game. The theorem replaces the infinite online interaction by static certificates.
--
--   Differences from the source:
--   - encoding: h(V) = u(V) log(2+V), u : [1, ∞) → (0, ∞) nondecreasing → IsLogThreshold h: ∃ u : ℝ → ℝ positive and monotone on [1, ∞) with h V = u V · log(2 + V) for V ≥ 1; reason: same class; values of u below 1 and of h at 0 are never used
--   - encoding: profile q : X → [0, 1] → q : Set (Fin d → ℤ) → ℝ with 0 ≤ q L ≤ 1 for L ∈ X; reason: values off X are never used
--   - encoding: countable rooted tree with vertex labels → DecoratedTree: vertices are a prefix-closed set of finite sequences of naturals (root []), children v ++ [n]; reason: every countable rooted tree is isomorphic to one of this form, and every such tree is countable
--   - reading: Definition 7.14: "defined as in Definition 7.5, except that … equal underlying language labels are permitted along an edge … for every copy (M, n) with P_v ⊆ M ⊆ L_v a child labelled (M, n)" → children have L_w ⊆ L_v and a_w > a_v; coverage over all M ∈ X with P_v ⊆ M ⊆ L_v and all n ≥ 1; path feasibility on the non-strict chain of underlying languages with copy quotas per level; reason: the only reading consistent with the page (SUPPLEMENT.md decision 3): the strict inclusion of Definition 7.5 is relaxed exactly where the page permits equal labels, and a level move between equal languages exposes nothing
--   - encoding: time t = 1, 2, … with inputs x_t, outputs o_t → 0-indexed time; the output at time t is G applied to x 0, …, x t; reason: index shift only; the same runs
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc309339291b1a61b8504342f4050ece6e4e903dd18b2bf541446f1064), §7, Theorem 7.2, p.52 (PDF p.54); Definition 7.14, p.67

import Mathlib
import Definitions.Def_LocalBreadth_Supplement_IsAchievable
import Definitions.Def_LocalBreadth_Supplement_IsCopyProtectedTree

namespace LocalBreadth.Supplement

/-- Theorem 7.2 (exact simultaneous profile characterization). Kleinberg, Wei, STOC 2027 submission
(manuscript sha256 f924cbfc…), §7, p.52. Under the standing assumptions of §7 (`d ≥ 2`, `X` a nonempty
countable family of infinite subsets of `ℤ^d`, `h(V) = u(V) log(2 + V)` with `u` positive and
nondecreasing), a profile `α : X → [0, 1]` is achieved by one globally fresh, universally eventually
valid generator if and only if every accuracy copy `(K, k)`, `K ∈ X`, `k ≥ 1`, has a protected tree on
copies (Definition 7.14). -/
theorem theorem_7_2 (d : ℕ) (hd : 2 ≤ d) (X : Set (Set (Fin d → ℤ))) (hne : X.Nonempty)
    (hc : X.Countable) (hinf : ∀ L ∈ X, L.Infinite) (h : ℕ → ℝ) (hh : IsLogThreshold h)
    (α : Set (Fin d → ℤ) → ℝ) (hα : ∀ L ∈ X, 0 ≤ α L ∧ α L ≤ 1) :
    IsAchievable h X α ↔
      ∀ K ∈ X, ∀ k : ℕ, 1 ≤ k → ∃ T idx, IsCopyProtectedTree h α X K k T idx := by sorry

end LocalBreadth.Supplement
