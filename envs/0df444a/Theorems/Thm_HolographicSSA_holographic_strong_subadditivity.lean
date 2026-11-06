-- Prove2me | Theorems.Thm_HolographicSSA_holographic_strong_subadditivity
-- name    : HolographicSSA.holographic_strong_subadditivity
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T05:33:44.824874+00:00
-- url     : https://prove2.me/theorems/94d03e9b-1dfa-400b-ba2d-4a4691f05a33
-- title:
--   Holographic strong subadditivity, eq. (3.1) — both inequalities
-- statement:
--   Let $X$ be a topological space (the constant-time slice of the bulk, cut off at a finite value of the holographic coordinate) carrying a measure $\mu$ (the area) for which every open set is measurable, let $\Gamma\subseteq X$ be its conformal-boundary part, let $G>0$ be Newton's constant, and let $\mathcal R$ be a class of bulk regions. For $A\subseteq X$ let
--   $$
--   S(A)=\frac{1}{4G}\,\inf\bigl\{\mu(\partial r)\;:\;r\in\mathcal R,\ r\cap\Gamma=A\bigr\}\in[0,\infty]
--   $$
--   be the holographic entanglement entropy (2.1) with the homology rule. Then for all $A,B\subseteq X$:
--
--   1. if $\mathcal R$ is closed under union and intersection, then
--   $$
--   S(A)+S(B)\ \ge\ S(A\cup B)+S(A\cap B);
--   $$
--   2. if $\mathcal R$ is closed under set difference, then
--   $$
--   S(A)+S(B)\ \ge\ S(A\setminus B)+S(B\setminus A),\qquad A\setminus B=A\cap B^{c}.
--   $$
--
--   These are the two forms (3.1) of strong subadditivity, the property every quantum entanglement entropy has; the theorem shows that the Ryu–Takayanagi prescription has it for every static bulk geometry, which is the paper's consistency check of holographic entanglement entropy.
--
--   **Formalization Note** Both inequalities are stated in $[0,\infty]$. Each closure hypothesis on $\mathcal R$ is attached only to the inequality that uses it, so the first inequality also covers classes (such as closed sets) that are not closed under difference.
--
--   Differences from the source:
--   - generalization: a static bulk slice cut off at finite holographic coordinate, with conformal boundary → an arbitrary topological space $X$ and an arbitrary subset $\Gamma\subseteq X$; reason: the paper's slice is a topological space and its cutoff boundary a subset of it
--   - generalization: the area $a$ → an arbitrary measure on $X$ with open sets measurable; reason: the paper notes the argument holds for "any extensive functional of the hypersurface" (p.6), and the Riemannian area (a multiple of $\mu_H^{d-1}$) is such a measure
--   - generalization: regions of the bulk → an arbitrary class $\mathcal R$, closed under $\cup$ and $\cap$ for the first inequality and under $\setminus$ for the second; reason: the proof uses only these closures (3.2); the class of all subsets satisfies both
--   - generalization: boundary regions $A,B$ → arbitrary subsets $A,B\subseteq X$; reason: for $A\not\subseteq\Gamma$ no region is homologous to $A$, so $S(A)=\infty$ and the inequalities hold; for boundary regions they are the paper's
--   - encoding: $\frac{1}{4G_N}\min_m a(m)$ over hypersurfaces homologous to $A$ → $\frac{1}{4G}$ times the infimum in $[0,\infty]$ of $\mu(\partial r)$ over $r\in\mathcal R$ with $r\cap\Gamma=A$, $\partial$ the frontier in $X$; reason: the definition's convention (the minimum, when it exists, is the infimum; $\partial r=A\cup m$ is read as frontier plus the homology rule)
--   - encoding: $A\cap B^{c}$ with the complement in the boundary → $A\setminus B$ in $X$; reason: the same set, since $A\cap B^c$ does not depend on the ambient space of the complement
-- source:
--   Headrick, Takayanagi, A holographic proof of the strong subadditivity of entanglement entropy, arXiv:0704.3719v1, §3, eq. (3.1), p.5 (PDF p.6)

import Mathlib
import Definitions.Def_HolographicSSA_holographicEntropy

open MeasureTheory

namespace HolographicSSA

/-- **Holographic strong subadditivity** (Headrick, Takayanagi, *A holographic proof of the strong
subadditivity of entanglement entropy*, arXiv:0704.3719v1, §3, eq. (3.1), p.5): "We begin by
rewriting the inequalities (1.3) in the forms S(A) + S(B) ≥ S(A ∪ B) + S(A ∩ B) ,
S(A) + S(B) ≥ S(A \ B) + S(B \ A) , (3.1) where A \ B ≡ A ∩ Bc."

Let `X` be a topological space (the cut-off bulk slice) with a measure `μ` (the area) whose open
sets are measurable, `Γ ⊆ X` its conformal-boundary part, `0 < G` (Newton's constant), and `𝓡` a
class of bulk regions. Writing `S = holographicEntropy Γ μ G 𝓡`, for all `A, B ⊆ X`:
1. if `𝓡` is closed under `∪` and `∩`, then `S (A ∪ B) + S (A ∩ B) ≤ S A + S B`;
2. if `𝓡` is closed under `\`, then `S (A \ B) + S (B \ A) ≤ S A + S B`.

**Formalization Note** See `HolographicSSA.holographicEntropy` for the encoding (frontier in `X` as
the surface, `r ∩ Γ = A` as the homology rule, an arbitrary measure as the area, `⨅` in `ℝ≥0∞` as
`min`). Each closure hypothesis is attached only to the inequality whose proof uses it. -/
theorem holographic_strong_subadditivity {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (Γ : Set X) (μ : Measure X) (G : ℝ) (hG : 0 < G)
    (𝓡 : Set (Set X)) (A B : Set X) :
    ((∀ r ∈ 𝓡, ∀ s ∈ 𝓡, r ∪ s ∈ 𝓡 ∧ r ∩ s ∈ 𝓡) →
        holographicEntropy Γ μ G 𝓡 (A ∪ B) + holographicEntropy Γ μ G 𝓡 (A ∩ B) ≤
          holographicEntropy Γ μ G 𝓡 A + holographicEntropy Γ μ G 𝓡 B) ∧
      ((∀ r ∈ 𝓡, ∀ s ∈ 𝓡, r \ s ∈ 𝓡) →
        holographicEntropy Γ μ G 𝓡 (A \ B) + holographicEntropy Γ μ G 𝓡 (B \ A) ≤
          holographicEntropy Γ μ G 𝓡 A + holographicEntropy Γ μ G 𝓡 B) := by sorry

end HolographicSSA
