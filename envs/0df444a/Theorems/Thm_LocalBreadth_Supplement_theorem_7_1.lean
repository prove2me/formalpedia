-- Prove2me | Theorems.Thm_LocalBreadth_Supplement_theorem_7_1
-- name    : LocalBreadth.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:25:54.740312+00:00
-- url     : https://prove2.me/theorems/f2cdee3d-8f7c-45be-8ba7-a5d78184357e
-- title:
--   Theorem 7.1 — protected trees for fixed quotas, both directions
-- statement:
--   Throughout, as in all of §7, $d\ge2$, $\mathcal X$ is a nonempty countable family of infinite subsets of $\mathbb Z^d$, and the threshold is $h(V)=u(V)\log(2+V)$ with $u:[1,\infty)\to(0,\infty)$ nondecreasing.
--
--   1. Let $q:\mathcal X\to[0,1]$ be a quota profile. If every $K\in\mathcal X$ has a $q$-protected tree (Definition 7.5), then one globally fresh, universally eventually valid generator satisfies
--   $$\delta_h(O,K)\ge q(K)$$
--   on every full enumeration of every $K\in\mathcal X$.
--   2. Conversely, let $\alpha:\mathcal X\to[0,1]$ be an achievable profile. Then for every $\varepsilon>0$ every $K\in\mathcal X$ has a $q_\varepsilon$-protected tree, where $q_\varepsilon(L)=(\alpha(L)-\varepsilon)_+$.
--
--   The first direction turns static certificates into a generator; the second shows that, up to an arbitrary loss $\varepsilon$, such certificates are necessary.
--
--   Differences from the source:
--   - encoding: h(V) = u(V) log(2+V), u : [1, ∞) → (0, ∞) nondecreasing → IsLogThreshold h: ∃ u : ℝ → ℝ positive and monotone on [1, ∞) with h V = u V · log(2 + V) for V ≥ 1; reason: same class; values of u below 1 and of h at 0 are never used
--   - encoding: profile q : X → [0, 1] → q : Set (Fin d → ℤ) → ℝ with 0 ≤ q L ≤ 1 for L ∈ X; reason: values off X are never used
--   - encoding: countable rooted tree with vertex labels → DecoratedTree: vertices are a prefix-closed set of finite sequences of naturals (root []), children v ++ [n]; reason: every countable rooted tree is isomorphic to one of this form, and every such tree is countable
--   - encoding: time t = 1, 2, … with inputs x_t, outputs o_t → 0-indexed time; the output at time t is G applied to x 0, …, x t; reason: index shift only; the same runs
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc309339291b1a61b8504342f4050ece6e4e903dd18b2bf541446f1064), §7, Theorem 7.1, p.52 (PDF p.54)

import Mathlib
import Definitions.Def_LocalBreadth_Supplement_IsAchievable
import Definitions.Def_LocalBreadth_Supplement_IsProtectedTree

namespace LocalBreadth.Supplement

/-- Theorem 7.1. Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…), §7, p.52. Fix
`d ≥ 2`, a nonempty countable family `X` of infinite subsets of `ℤ^d`, and a threshold
`h(V) = u(V) log(2 + V)` with `u : [1, ∞) → (0, ∞)` nondecreasing (standing assumptions of §7, p.51).
1. For a quota profile `q : X → [0, 1]`: if every `K ∈ X` has a `q`-protected tree (Definition 7.5),
   then one globally fresh, universally eventually valid generator satisfies `δ_h(O, K) ≥ q(K)` on every
   full enumeration of every `K ∈ X`.
2. Conversely, if `α` is an achievable profile, then for every `ε > 0` every `K ∈ X` has a
   `q_ε`-protected tree, `q_ε(L) = (α(L) - ε)_+`.

**Formalization Note.** Profiles are functions `Set (Fin d → ℤ) → ℝ` with values in `[0, 1]` on `X`. -/
theorem theorem_7_1 (d : ℕ) (hd : 2 ≤ d) (X : Set (Set (Fin d → ℤ))) (hne : X.Nonempty)
    (hc : X.Countable) (hinf : ∀ L ∈ X, L.Infinite) (h : ℕ → ℝ) (hh : IsLogThreshold h) :
    (∀ q : Set (Fin d → ℤ) → ℝ, (∀ L ∈ X, 0 ≤ q L ∧ q L ≤ 1) →
      (∀ K ∈ X, ∃ T, IsProtectedTree h q X K T) →
      ∃ G : GeneratorP (Fin d → ℤ), IsFreshP X G ∧ IsEventuallyValidP X G ∧
        ∀ K ∈ X, ∀ x, IsFullEnumerationP K x → q K ≤ deltaH h (outputSetP G x) K) ∧
    (∀ α : Set (Fin d → ℤ) → ℝ, (∀ L ∈ X, 0 ≤ α L ∧ α L ≤ 1) → IsAchievable h X α →
      ∀ ε : ℝ, 0 < ε → ∀ K ∈ X, ∃ T, IsProtectedTree h (fun L => max (α L - ε) 0) X K T) := by sorry

end LocalBreadth.Supplement
