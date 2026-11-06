-- Prove2me | Theorems.Thm_HolographicSSA_area_rearrangement_le
-- name    : HolographicSSA.area_rearrangement_le
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T05:32:57.140659+00:00
-- url     : https://prove2.me/theorems/70bf46d5-dc16-4f7f-a43a-879d3d412054
-- title:
--   Footnote 3 — $a(m_{A\cup B})+a(m_{A\cap B})\le a(m_A)+a(m_B)$
-- statement:
--   Let $X$ be a topological space and $\mu$ a measure on $X$ for which every open set is measurable, and write $\partial$ for the topological frontier. For all $r,s\subseteq X$,
--   $$
--   \mu\bigl(\partial(r\cup s)\bigr)+\mu\bigl(\partial(r\cap s)\bigr)\le\mu(\partial r)+\mu(\partial s).
--   $$
--
--   With $r=r_A$, $s=r_B$ and $\mu$ the area $a$, this is footnote 3's inequality $a(m_{A\cup B})+a(m_{A\cap B})\le a(m_A)+a(m_B)$: the surfaces of the union and intersection regions cost no more, together, than the minimal surfaces they are cut from. It is the step that closes the proof of strong subadditivity.
--
--   **Formalization Note** The paper's equality (3.4) holds only in the "generic situation" of footnote 3, which is not defined, and it fails in general (two unit squares in the plane touching along a side); this item is the footnote's general inequality, which the proof uses.
--
--   Differences from the source:
--   - generalization: the area $a$ of hypersurfaces in the bulk slice → an arbitrary measure $\mu$ on a topological space in which open sets are measurable; reason: the paper notes (3.4) holds for "any extensive functional of the hypersurface" (p.6), and the Riemannian area is a Borel measure (a multiple of $\mu_H^{d-1}$), so it is an instance
--   - generalization: the surfaces of the regions $r_A$, $r_B$ and of $r_A\cup r_B$, $r_A\cap r_B$ → the frontiers of arbitrary subsets $r,s$ and of $r\cup s$, $r\cap s$; reason: the paper's inequality is the instance $r=r_A$, $s=r_B$
-- source:
--   Headrick, Takayanagi, A holographic proof of the strong subadditivity of entanglement entropy, arXiv:0704.3719v1, footnote 3 to eq. (3.4), p.6 (PDF p.7)

import Mathlib

open MeasureTheory

namespace HolographicSSA

/-- **Area inequality for the rearranged surfaces** (Headrick, Takayanagi, arXiv:0704.3719v1,
footnote 3 to eq. (3.4), p.6): "More generally we have mA∪B ∪ mA∩B ⊂ mA ∪ mB and
a(mA∪B) + a(mA∩B) ≤ a(mA) + a(mB)."

For every measure `μ` on a topological space `X` whose open sets are measurable, and all subsets
`r, s ⊆ X`,
`μ (frontier (r ∪ s)) + μ (frontier (r ∩ s)) ≤ μ (frontier r) + μ (frontier s)`.

**Formalization Note** The area `a` is an arbitrary measure (the paper: (3.4) holds for "any
extensive functional of the hypersurface", p.6; the intended instance is the Riemannian area,
a multiple of `μH[d-1]`). The surface of a region is its topological frontier. The equality (3.4)
is asserted only in an undefined "generic situation" and is false in general; this is footnote 3's
general inequality. -/
theorem area_rearrangement_le {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) (r s : Set X) :
    μ (frontier (r ∪ s)) + μ (frontier (r ∩ s)) ≤ μ (frontier r) + μ (frontier s) := by sorry

end HolographicSSA
