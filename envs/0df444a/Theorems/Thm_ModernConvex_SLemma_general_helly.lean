-- Prove2me | Theorems.Thm_ModernConvex_SLemma_general_helly
-- name    : ModernConvex.SLemma.general_helly
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:06.686713+00:00
-- url     : https://prove2.me/theorems/f2c84ad4-5438-403c-88d4-348d1a380bab
-- title:
--   Theorem 4.10.1 — general Helly theorem for infinite families of closed convex sets
-- statement:
--   Let $\{A_\alpha\}_{\alpha\in I}$ be a family (possibly infinite) of closed convex subsets of $\mathbb R^n$ such that
--
--   1. every $n+1$ sets from the family have a point in common, and
--   2. there is a finite subfamily whose intersection is bounded.
--
--   Then all sets of the family have a point in common:
--   $$\bigcap_{\alpha\in I} A_\alpha \neq \emptyset.$$
--
--   The finite Helly theorem needs neither closedness nor boundedness. For infinite families both are needed: the half-lines $[k, \infty)$, $k \in \mathbb N$, have the finite intersection property but empty intersection. The book uses this theorem to give a straightforward proof of the S-lemma (Exercises 4.45–4.46).
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`. Its sup-norm bornology has the same bounded sets as the Euclidean one. "Every $n+1$ sets" is every map `Fin (n + 1) → I`, so repeated indices are allowed and a family with fewer than $n+1$ members is covered. The finite subfamily is a `Finset I`. The index type `I` is arbitrary and may be empty. This is not the platform's `FamousTheorems.helly_theorem`, which treats finite families.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 305, Theorem 4.10.1 (Exercise 4.44)

import Mathlib

namespace ModernConvex.SLemma

/-- Ben-Tal–Nemirovski, Theorem 4.10.1 (General Helley theorem), p. 305: let `{A_α}_{α ∈ I}` be a
family of closed convex sets in `ℝⁿ` such that (1) every `n + 1` sets from the family have a
point in common, and (2) some finite subfamily has a bounded intersection. Then all sets of the
family have a point in common. "Every `n + 1` sets" is every choice of `n + 1` indices, repetitions
allowed (so a family with fewer than `n + 1` members is covered). -/
theorem general_helly {n : ℕ} {I : Type} (A : I → Set (Fin n → ℝ))
    (hclosed : ∀ α, IsClosed (A α)) (hconvex : ∀ α, Convex ℝ (A α))
    (hinter : ∀ f : Fin (n + 1) → I, (⋂ k, A (f k)).Nonempty)
    (hbdd : ∃ s : Finset I, Bornology.IsBounded (⋂ α ∈ s, A α)) :
    (⋂ α, A α).Nonempty := by sorry

end ModernConvex.SLemma
