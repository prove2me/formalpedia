-- Prove2me | Theorems.Thm_MetricGenerators_IsometryExt_represents_subset_cStar
-- name    : MetricGenerators.IsometryExt.represents_subset_cStar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:45.986597+00:00
-- url     : https://prove2.me/theorems/7c90ad6c-6030-4812-a336-260ce5e24e25
-- title:
--   §2, proof of Theorem 4, p. 388 — every representation satisfies C_u ⊆ C*_u
-- statement:
--   Let $H$ and $G$ be finite connected graphs, $T$ a strong metric generator of $H$, $f:(T,\mu_H|_T)\to G$ an isometry, and let the sets $C_u$ ($u\in V(H)$) represent $H$ in $G$ with respect to $T$. Then
--   $$C_u\subseteq C^*_u\qquad\text{for every } u\in V(H),$$
--   where $C^*_u=C^{(|V(G)|)}_u$ is the output of the candidate procedure.
--
--   The procedure therefore never discards a vertex that some representation uses; this is the maximality half of the second paragraph of Theorem 4. No forest hypothesis is needed.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 388, §2, proof of Theorem 4 (unnumbered, first paragraph)

import Mathlib
import Definitions.Def_MetricGenerators_IsometryExt_Basic
import Definitions.Def_MetricGenerators_IsometryExt_Representation

namespace MetricGenerators.IsometryExt

/-- Sebő and Tannier, *On Metric Generators of Graphs*, Math. Oper. Res. 29(2):383–393 (2004),
DOI 10.1287/moor.1030.0070, §2, proof of Theorem 4, p. 388 (unnumbered): if the sets `C_u` represent `H` in `G`
with respect to `T`, then by (i) `C_u ⊆ C^(0)_u`, `C_u ⊆ C^(i)_u` implies `C_u ⊆ C^(i+1)_u`, and
therefore `C_u ⊆ C*_u` for every `u ∈ V(H)`.

Formalization Note: `H` and `G` are finite and connected (p. 383); `T` is a strong metric
generator and `f` an isometry on `T`, the standing data of §2. The generator property is needed:
the recursion for `C^(i+1)` tests every `u'` with `x ∈ C^(i)_u'`, and the disjointness of the
sets `C^(0)_u` is what forces `u' = u`. There is no forest hypothesis. -/
theorem represents_subset_cStar {VH VG : Type*} [Fintype VH] [Fintype VG]
    (H : SimpleGraph VH) (G : SimpleGraph VG) (hH : H.Connected) (hG : G.Connected)
    (T : Finset VH) (hT : IsStrongMetricGenerator H T) (f : ↥T → VG)
    (hf : IsIsometryOn H G T f) (C : VH → Set VG) (hC : Represents H G T f C) :
    ∀ u : VH, C u ⊆ cStar H G T f u := by sorry

end MetricGenerators.IsometryExt
