-- Prove2me | Theorems.Thm_MetricGenerators_IsometryExt_represents_singleton_disjoint
-- name    : MetricGenerators.IsometryExt.represents_singleton_disjoint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:49.528521+00:00
-- url     : https://prove2.me/theorems/06728516-c206-4929-816a-070e427a342b
-- title:
--   §2, p. 387 — a representation has C_t = {f(t)} for t ∈ T and pairwise disjoint C_u
-- statement:
--   Let $H$ and $G$ be finite connected graphs, $T\subseteq V(H)$ a metric generator of $H$, $f:(T,\mu_H|_T)\to G$ an isometry, and let the sets $C_u$ ($u\in V(H)$) represent $H$ in $G$ with respect to $T$. Then
--   $$C_t=\{f(t)\}\ \ (t\in T)\qquad\text{and}\qquad C_u\cap C_v=\emptyset\ \ (u\ne v).$$
--
--   Condition (i) of a representation alone forces the vertices of $T$ to their prescribed images and keeps the candidate sets of distinct vertices apart.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 387, §2 (unnumbered, after the definition of a representation)

import Mathlib
import Definitions.Def_MetricGenerators_IsometryExt_Basic
import Definitions.Def_MetricGenerators_IsometryExt_Representation

namespace MetricGenerators.IsometryExt

/-- Sebő and Tannier, *On Metric Generators of Graphs*, Math. Oper. Res. 29(2):383–393 (2004),
DOI 10.1287/moor.1030.0070, §2, p. 387 (unnumbered): since `T` is a metric generator in `H` and `f` is an isometry on
`T`, if the sets `C_u` represent `H` in `G` with respect to `T`, then `C_t = {f(t)}` for all
`t ∈ T`, and `C_u ∩ C_v = ∅` whenever `u ≠ v`.

Formalization Note: `H` and `G` are finite and connected (standing assumption, p. 383). The
nonemptiness built into `Represents` is what gives `C_t = {f(t)}` rather than `C_t ⊆ {f(t)}`. -/
theorem represents_singleton_disjoint {VH VG : Type*} [Fintype VH] [Fintype VG]
    (H : SimpleGraph VH) (G : SimpleGraph VG) (hH : H.Connected) (hG : G.Connected)
    (T : Finset VH) (hT : IsMetricGenerator H T) (f : ↥T → VG) (hf : IsIsometryOn H G T f)
    (C : VH → Set VG) (hC : Represents H G T f C) :
    (∀ t : ↥T, C t = {f t}) ∧ (∀ u v : VH, u ≠ v → Disjoint (C u) (C v)) := by sorry

end MetricGenerators.IsometryExt
