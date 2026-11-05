-- Prove2me | Theorems.Thm_HolographicSSA_rearranged_region_bound
-- name    : HolographicSSA.rearranged_region_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:40.194077+00:00
-- url     : https://prove2.me/theorems/ae5321d7-f085-438e-9d77-26b1a8179150
-- title:
--   The regions $r_A\cup r_B$ and $r_A\cap r_B$ bound $4G_N\,S(A\cup B)$ and $4G_N\,S(A\cap B)$
-- statement:
--   Let $S$ be the holographic entanglement entropy on a bulk $X$ with boundary part $\Gamma$, area measure $\mu$, Newton's constant $G>0$ and admissible regions $\mathcal R$. Let $A,B\subseteq X$ and let $r,s\subseteq X$ be homologous to them: $r\cap\Gamma=A$ and $s\cap\Gamma=B$. Then
--
--   1. if $r\cup s\in\mathcal R$, then $4G\,S(A\cup B)\le\mu\bigl(\partial(r\cup s)\bigr)$;
--   2. if $r\cap s\in\mathcal R$, then $4G\,S(A\cap B)\le\mu\bigl(\partial(r\cap s)\bigr)$.
--
--   With $r=r_A$, $s=r_B$ the regions of the minimal surfaces $m_A$, $m_B$, these are the regions (3.2) $r_{A\cup B}=r_A\cup r_B$ and $r_{A\cap B}=r_A\cap r_B$, whose bulk surfaces $m_{A\cup B}$, $m_{A\cap B}$ (3.3) end on $\partial(A\cup B)$ and $\partial(A\cap B)$: their areas bound $4G_N\,S(A\cup B)$ and $4G_N\,S(A\cap B)$ from above, although they need not be minimal.
--
--   **Formalization Note** The factor $4G_N$ is `ENNReal.ofReal (4 * G)`, and the inequalities are in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: $r_A$, $r_B$ the regions of the minimal hypersurfaces $m_A$, $m_B$ → any sets $r$, $s$ with $r\cap\Gamma=A$ and $s\cap\Gamma=B$; reason: minimality of $m_A$, $m_B$ is not used by this step, and the paper's regions are an instance
--   - generalization: $r_A\cup r_B$ and $r_A\cap r_B$ are regions of the bulk → membership of $r\cup s$ (resp. $r\cap s$) in the admissible class $\mathcal R$ is a hypothesis of the corresponding clause; reason: the class $\mathcal R$ is arbitrary, and for the class of all subsets (the paper's unrestricted regions) the hypothesis always holds
--   - encoding: $\min_m a(m)$ over hypersurfaces homologous to $A$ → the infimum in $[0,\infty]$ of $\mu(\partial r)$ over $r\in\mathcal R$ with $r\cap\Gamma=A$; reason: the definition's convention, equal to the minimum whenever one exists
-- source:
--   Headrick, Takayanagi, A holographic proof of the strong subadditivity of entanglement entropy, arXiv:0704.3719v1, p.6 (PDF p.7), with eqs. (3.2)–(3.3), p.5 (PDF p.6)

import Mathlib
import Definitions.Def_HolographicSSA_holographicEntropy

open MeasureTheory

namespace HolographicSSA

/-- **The rearranged regions are competitors** (Headrick, Takayanagi, arXiv:0704.3719v1, p.6, with
(3.2)–(3.3), p.5): "Clearly mA∪B ends on ∂(A ∪ B). While nothing says that it is the minimal
hypersurface ending on ∂(A ∪ B), its area is an upper bound on the area of the minimal one, and
therefore on 4GN S(A ∪ B); similarly for A ∩ B." Here rA∪B = rA ∪ rB and rA∩B = rA ∩ rB (3.2),
with ∂rA∪B = (A ∪ B) ∪ mA∪B and ∂rA∩B = (A ∩ B) ∪ mA∩B (3.3).

Let `S = holographicEntropy Γ μ G 𝓡` with `0 < G`, and let `r, s ⊆ X` satisfy the homology rule
for `A` and `B`: `r ∩ Γ = A`, `s ∩ Γ = B`. Then
1. if `r ∪ s ∈ 𝓡`, then `4G · S (A ∪ B) ≤ μ (frontier (r ∪ s))`;
2. if `r ∩ s ∈ 𝓡`, then `4G · S (A ∩ B) ≤ μ (frontier (r ∩ s))`.

**Formalization Note** See `HolographicSSA.holographicEntropy` for the encoding (frontier in `X` as
the surface, `r ∩ Γ = A` as the homology rule, `⨅` in `ℝ≥0∞` as `min`). The factor `4G_N` is
`ENNReal.ofReal (4 * G)`. -/
theorem rearranged_region_bound {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (Γ : Set X) (μ : Measure X) (G : ℝ) (hG : 0 < G) (𝓡 : Set (Set X))
    (A B r s : Set X) (hr : r ∩ Γ = A) (hs : s ∩ Γ = B) :
    (r ∪ s ∈ 𝓡 →
        ENNReal.ofReal (4 * G) * holographicEntropy Γ μ G 𝓡 (A ∪ B) ≤ μ (frontier (r ∪ s))) ∧
      (r ∩ s ∈ 𝓡 →
        ENNReal.ofReal (4 * G) * holographicEntropy Γ μ G 𝓡 (A ∩ B) ≤ μ (frontier (r ∩ s))) := by sorry

end HolographicSSA
