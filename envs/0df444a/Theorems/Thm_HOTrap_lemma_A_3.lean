-- Prove2me | Theorems.Thm_HOTrap_lemma_A_3
-- name    : HOTrap.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:47:55.244201+00:00
-- url     : https://prove2.me/theorems/61f33911-e541-4513-ac64-fef9426e423a
-- title:
--   Lemma A.3 — Hölder Taylor remainder
-- statement:
--   Let $p\ge0$ be an integer, $\beta\in(0,1]$, $L\ge0$, let $S\subset\mathbb R^d$ be convex, and let $F\in C^{p,\beta}(L)$ on a neighbourhood of $S$. For $c\in S$, let $T_p$ be the degree-$p$ Taylor polynomial of $F$ at $c$. Then
--   $$
--   \|D^j(F-T_p)(c+v)\|\le a_{p-j,\beta}\,L\,\|v\|_2^{p-j+\beta}\qquad(0\le j\le p,\ c+v\in S).
--   $$
--
--   The Taylor polynomial is the comparison polynomial behind every reconstruction bound of the mission.
--
--   **Formalization Note** $D^j$ is `iteratedFDeriv ℝ j` with the multilinear operator norm.
--
--   Differences from the source:
--   - generalization: F scalar- or vector-valued, with Euclidean output norms → F takes values in any real Banach space G; reason: ℝ and ℝ^m are Banach spaces, so the printed statement is the instance G = ℝ^m
--   - encoding: "on a neighborhood of S" → an open set U containing S; reason: the standard meaning of the phrase
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Lemma A.3, Eq. (54), p.54

import Mathlib
import Definitions.Def_HOTrap_HolderNear
import Definitions.Def_HOTrap_taylorConst
import Definitions.Def_HOTrap_taylorPoly

namespace HOTrap

/-- **Lemma A.3 (Hölder Taylor remainder).** Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Lemma A.3, Eq. (54), p.54. Let `p ≥ 0`, let `S ⊂ ℝ^d` be
convex and `F ∈ C^{p,β}(L)` on a neighbourhood of `S`. For `c ∈ S` and the degree-`p` Taylor polynomial `T_p`
of `F` at `c`, `∥D^j(F − T_p)(c + v)∥ ≤ a_{p−j,β} L ∥v∥₂^{p−j+β}` for `0 ≤ j ≤ p` and `c + v ∈ S`.

**Formalization Note** `F` takes values in any real Banach space `G`. `D^j` is `iteratedFDeriv ℝ j` with the
multilinear operator norm; `c + v ∈ S` lies in the open neighbourhood, so it is the true derivative. -/
theorem lemma_A_3 {d : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (p : ℕ) (β L : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hL : 0 ≤ L)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : Convex ℝ S) (F : EuclideanSpace ℝ (Fin d) → G) (hF : HolderNear S p β L F)
    (c : EuclideanSpace ℝ (Fin d)) (hc : c ∈ S) (j : ℕ) (hj : j ≤ p) (v : EuclideanSpace ℝ (Fin d)) (hv : c + v ∈ S) :
    ‖iteratedFDeriv ℝ j (fun y => F y - taylorPoly F p c y) (c + v)‖ ≤
      taylorConst (p - j) β * L * ‖v‖ ^ (((p - j : ℕ) : ℝ) + β) := by sorry

end HOTrap
