-- Prove2me | Theorems.Thm_HolographicSSA_ssa_union_inter
-- name    : HolographicSSA.ssa_union_inter
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:32.994514+00:00
-- url     : https://prove2.me/theorems/096d01e9-8fd8-4469-b58a-4cb7005d628c
-- title:
--   Eq. (3.1), first inequality — $S(A)+S(B)\ge S(A\cup B)+S(A\cap B)$
-- statement:
--   Let $X$ be a topological space (the cut-off bulk slice) carrying a measure $\mu$ (the area) for which every open set is measurable, let $\Gamma\subseteq X$ be its conformal-boundary part, let $G>0$ be Newton's constant, and let $\mathcal R$ be a class of bulk regions closed under union and intersection: $r\cup s\in\mathcal R$ and $r\cap s\in\mathcal R$ whenever $r,s\in\mathcal R$. Let $S$ be the holographic entanglement entropy built from these data. Then for all $A,B\subseteq X$,
--   $$
--   S(A)+S(B)\ \ge\ S(A\cup B)+S(A\cap B)
--   $$
--   in $[0,\infty]$.
--
--   This is strong subadditivity of the Ryu–Takayanagi entropy in its union–intersection form, the first of the two inequalities (3.1).
--
--   **Formalization Note** The inequality is stated in $[0,\infty]$; when one side involves a region with no homologous admissible bulk region its entropy is $\infty$.
--
--   Differences from the source:
--   - generalization: a static bulk slice cut off at finite holographic coordinate, with conformal boundary → an arbitrary topological space $X$ and an arbitrary subset $\Gamma\subseteq X$; reason: the paper's slice is a topological space and its cutoff boundary a subset of it
--   - generalization: the area $a$ → an arbitrary measure on $X$ with open sets measurable; reason: the paper notes the argument holds for "any extensive functional of the hypersurface" (p.6), and the Riemannian area (a multiple of $\mu_H^{d-1}$) is such a measure
--   - generalization: regions of the bulk → an arbitrary class $\mathcal R$ closed under $\cup$ and $\cap$; reason: the proof uses only that $r_A\cup r_B$ and $r_A\cap r_B$ are regions (3.2); the class of all subsets is an instance
--   - generalization: boundary regions $A,B$ → arbitrary subsets $A,B\subseteq X$; reason: for $A\not\subseteq\Gamma$ no region is homologous to $A$, so $S(A)=\infty$ and the inequality holds; for boundary regions it is the paper's
--   - encoding: $\frac{1}{4G_N}\min_m a(m)$ over hypersurfaces homologous to $A$ → $\frac{1}{4G}$ times the infimum in $[0,\infty]$ of $\mu(\partial r)$ over $r\in\mathcal R$ with $r\cap\Gamma=A$, $\partial$ the frontier in $X$; reason: the definition's convention (the minimum, when it exists, is the infimum; $\partial r=A\cup m$ is read as frontier plus the homology rule)
-- source:
--   Headrick, Takayanagi, A holographic proof of the strong subadditivity of entanglement entropy, arXiv:0704.3719v1, eq. (3.1), first inequality, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_HolographicSSA_holographicEntropy

open MeasureTheory

namespace HolographicSSA

/-- **Strong subadditivity, union–intersection form** (Headrick, Takayanagi, arXiv:0704.3719v1,
eq. (3.1), first inequality, p.5): "We begin by rewriting the inequalities (1.3) in the forms
S(A) + S(B) ≥ S(A ∪ B) + S(A ∩ B) ,".

Let `X` be a topological space with a measure `μ` whose open sets are measurable, `Γ ⊆ X`,
`0 < G`, and `𝓡` a class of bulk regions closed under union and intersection. Writing
`S = holographicEntropy Γ μ G 𝓡`, for all `A, B ⊆ X`
`S (A ∪ B) + S (A ∩ B) ≤ S A + S B` in `[0, ∞]`.

**Formalization Note** See `HolographicSSA.holographicEntropy` for the encoding. The class `𝓡` is
arbitrary apart from the closure under `∪` and `∩` that (3.2) uses; `A, B` are arbitrary sets (if
`A ⊄ Γ` then `S A = ∞`). -/
theorem ssa_union_inter {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (Γ : Set X) (μ : Measure X) (G : ℝ) (hG : 0 < G)
    (𝓡 : Set (Set X)) (h𝓡 : ∀ r ∈ 𝓡, ∀ s ∈ 𝓡, r ∪ s ∈ 𝓡 ∧ r ∩ s ∈ 𝓡) (A B : Set X) :
    holographicEntropy Γ μ G 𝓡 (A ∪ B) + holographicEntropy Γ μ G 𝓡 (A ∩ B) ≤
      holographicEntropy Γ μ G 𝓡 A + holographicEntropy Γ μ G 𝓡 B := by sorry

end HolographicSSA
