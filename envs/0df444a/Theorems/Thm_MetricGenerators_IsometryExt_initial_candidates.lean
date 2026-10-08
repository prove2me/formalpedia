-- Prove2me | Theorems.Thm_MetricGenerators_IsometryExt_initial_candidates
-- name    : MetricGenerators.IsometryExt.initial_candidates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:12.698734+00:00
-- url     : https://prove2.me/theorems/9cc30202-bf30-4ec4-8f26-9f2980aa3137
-- title:
--   §2, p. 387 — the C^(0)_u are pairwise disjoint and C^(0)_t = {f(t)} for t ∈ T
-- statement:
--   Let $H$ and $G$ be finite connected graphs, $T\subseteq V(H)$ a metric generator of $H$, and $f:(T,\mu_H|_T)\to G$ an isometry. Let $C^{(0)}_u=\{v\in V(G):\mu_G(f(t),v)=\mu_H(t,u)\ \forall t\in T\}$ be the initial candidate sets. Then
--
--   1. $C^{(0)}_u\cap C^{(0)}_v=\emptyset$ whenever $u\ne v$;
--   2. $C^{(0)}_t=\{f(t)\}$ for every $t\in T$.
--
--   These are the first observations about the candidate procedure: the candidates for distinct vertices never collide, and the vertices of $T$ have exactly their prescribed image as candidate.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 387, §2 (unnumbered, after the definition of C^(0)_u)

import Mathlib
import Definitions.Def_MetricGenerators_IsometryExt_Basic
import Definitions.Def_MetricGenerators_IsometryExt_Representation

namespace MetricGenerators.IsometryExt

/-- Sebő and Tannier, *On Metric Generators of Graphs*, Math. Oper. Res. 29(2):383–393 (2004),
DOI 10.1287/moor.1030.0070, §2, p. 387 (unnumbered): as `T` is a metric generator of `H`, the initial candidate
sets `C^(0)_u` (`u ∈ V(H)`) are pairwise disjoint; using also that `f` is an isometry on `T`,
`C^(0)_t = {f(t)}` for every `t ∈ T`.

Formalization Note: `H` and `G` are finite and connected (standing assumption, p. 383). The page
invokes only the metric-generator property of `T`, which is the hypothesis used here. -/
theorem initial_candidates {VH VG : Type*} [Fintype VH] [Fintype VG]
    (H : SimpleGraph VH) (G : SimpleGraph VG) (hH : H.Connected) (hG : G.Connected)
    (T : Finset VH) (hT : IsMetricGenerator H T) (f : ↥T → VG) (hf : IsIsometryOn H G T f) :
    (∀ u v : VH, u ≠ v → Disjoint (cand H G T f 0 u) (cand H G T f 0 v)) ∧
    (∀ t : ↥T, cand H G T f 0 t = {f t}) := by sorry

end MetricGenerators.IsometryExt
