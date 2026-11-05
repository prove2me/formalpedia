-- Prove2me | Theorems.Thm_HolographicSSA_ssa_diff
-- name    : HolographicSSA.ssa_diff
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:33.918725+00:00
-- url     : https://prove2.me/theorems/ebe6d4d0-2d1a-43bd-8cb3-8da32adf39c7
-- title:
--   Eq. (3.1), second inequality — $S(A)+S(B)\ge S(A\setminus B)+S(B\setminus A)$
-- statement:
--   Let $X$ be a topological space (the cut-off bulk slice) carrying a measure $\mu$ (the area) for which every open set is measurable, let $\Gamma\subseteq X$ be its conformal-boundary part, let $G>0$ be Newton's constant, and let $\mathcal R$ be a class of bulk regions closed under set difference: $r\setminus s\in\mathcal R$ whenever $r,s\in\mathcal R$. Let $S$ be the holographic entanglement entropy built from these data. Then for all $A,B\subseteq X$,
--   $$
--   S(A)+S(B)\ \ge\ S(A\setminus B)+S(B\setminus A)
--   $$
--   in $[0,\infty]$, where $A\setminus B=A\cap B^{c}$.
--
--   This is the second of the two inequalities (3.1), the holographic counterpart of the second form of strong subadditivity (weak monotonicity); the paper leaves its proof as an exercise.
--
--   **Formalization Note** The inequality is stated in $[0,\infty]$. For $A\subseteq\Gamma$, the set $A\setminus B$ is the paper's $A\cap B^{c}$ with the complement taken in the boundary.
--
--   Differences from the source:
--   - generalization: a static bulk slice cut off at finite holographic coordinate, with conformal boundary → an arbitrary topological space $X$ and an arbitrary subset $\Gamma\subseteq X$; reason: the paper's slice is a topological space and its cutoff boundary a subset of it
--   - generalization: the area $a$ → an arbitrary measure on $X$ with open sets measurable; reason: the paper notes the argument holds for "any extensive functional of the hypersurface" (p.6), and the Riemannian area (a multiple of $\mu_H^{d-1}$) is such a measure
--   - generalization: regions of the bulk → an arbitrary class $\mathcal R$ closed under $\setminus$; reason: differences of bulk regions are bulk regions; the class of all subsets is an instance
--   - generalization: boundary regions $A,B$ → arbitrary subsets $A,B\subseteq X$; reason: for $A\not\subseteq\Gamma$ no region is homologous to $A$, so $S(A)=\infty$ and the inequality holds; for boundary regions it is the paper's
--   - encoding: $\frac{1}{4G_N}\min_m a(m)$ over hypersurfaces homologous to $A$ → $\frac{1}{4G}$ times the infimum in $[0,\infty]$ of $\mu(\partial r)$ over $r\in\mathcal R$ with $r\cap\Gamma=A$, $\partial$ the frontier in $X$; reason: the definition's convention (the minimum, when it exists, is the infimum; $\partial r=A\cup m$ is read as frontier plus the homology rule)
--   - encoding: $A\cap B^{c}$ with the complement in the boundary → $A\setminus B$ in $X$; reason: the same set, since $A\cap B^c$ does not depend on the ambient space of the complement
-- source:
--   Headrick, Takayanagi, A holographic proof of the strong subadditivity of entanglement entropy, arXiv:0704.3719v1, eq. (3.1), second inequality, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_HolographicSSA_holographicEntropy

open MeasureTheory

namespace HolographicSSA

/-- **Strong subadditivity, difference form** (Headrick, Takayanagi, arXiv:0704.3719v1, eq. (3.1),
second inequality, p.5): "S(A) + S(B) ≥ S(A \ B) + S(B \ A) , (3.1) where A \ B ≡ A ∩ Bc. We will
prove the first inequality; the proof of the second one is very similar and is left as an exercise
to the reader."

Let `X` be a topological space with a measure `μ` whose open sets are measurable, `Γ ⊆ X`,
`0 < G`, and `𝓡` a class of bulk regions closed under set difference. Writing
`S = holographicEntropy Γ μ G 𝓡`, for all `A, B ⊆ X`
`S (A \ B) + S (B \ A) ≤ S A + S B` in `[0, ∞]`.

**Formalization Note** See `HolographicSSA.holographicEntropy` for the encoding. The class `𝓡` is
arbitrary apart from closure under `\`; `A \ B` is `A ∩ Bᶜ`, which for `A ⊆ Γ` is the paper's
`A ∩ Bc` with the complement taken in the boundary. -/
theorem ssa_diff {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (Γ : Set X) (μ : Measure X) (G : ℝ) (hG : 0 < G)
    (𝓡 : Set (Set X)) (h𝓡 : ∀ r ∈ 𝓡, ∀ s ∈ 𝓡, r \ s ∈ 𝓡) (A B : Set X) :
    holographicEntropy Γ μ G 𝓡 (A \ B) + holographicEntropy Γ μ G 𝓡 (B \ A) ≤
      holographicEntropy Γ μ G 𝓡 A + holographicEntropy Γ μ G 𝓡 B := by sorry

end HolographicSSA
