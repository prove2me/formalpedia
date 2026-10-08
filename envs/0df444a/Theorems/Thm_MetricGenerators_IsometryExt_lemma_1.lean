-- Prove2me | Theorems.Thm_MetricGenerators_IsometryExt_lemma_1
-- name    : MetricGenerators.IsometryExt.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:36.494032+00:00
-- url     : https://prove2.me/theorems/ad3354c5-a2a6-48b5-aa2c-870fae5312e0
-- title:
--   Lemma 1, p. 387 — in a representation, μ_H(u, v) = μ_G(x, C_v) for every x ∈ C_u
-- statement:
--   Let $H$ and $G$ be finite connected graphs, $T$ a strong metric generator of $H$, $f:(T,\mu_H|_T)\to G$ an isometry, and let nonempty sets $C_u$ ($u\in V(H)$) represent $H$ in $G$ with respect to $T$. Then for all $u,v\in V(H)$ and every $x\in C_u$,
--   $$\mu_H(u,v)=\mu_G(x,C_v):=\min\{\mu_G(x,y):\ y\in C_v\}.$$
--
--   The lemma is the intermediate stage between a representation and an isometry: each candidate for $u$ sits at exactly the right distance from the candidate set of every other vertex.
--
--   **Formalization Note** The minimum is stated as two facts: some $y\in C_v$ has $\mu_G(x,y)=\mu_H(u,v)$, and every $y\in C_v$ has $\mu_H(u,v)\le\mu_G(x,y)$. No forest hypothesis is needed.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 387, Lemma 1 (proof p. 388); μ_G(X, Y) defined on p. 387

import Mathlib
import Definitions.Def_MetricGenerators_IsometryExt_Basic
import Definitions.Def_MetricGenerators_IsometryExt_Representation

namespace MetricGenerators.IsometryExt

/-- Sebő and Tannier, *On Metric Generators of Graphs*, Math. Oper. Res. 29(2):383–393 (2004),
DOI 10.1287/moor.1030.0070, p. 387, **Lemma 1**: if nonempty sets `C_u` represent `H` in `G` with respect to the
strong metric generator `T`, then for all `u, v ∈ V(H)` and `x ∈ C_u`, `μ_H(u, v) = μ_G(x, C_v)`,
where `μ_G(x, C_v) = min {μ_G(x, y) : y ∈ C_v}`.

Formalization Note: the minimum is encoded as "attained and a lower bound": some `y ∈ C_v` has
`μ_G(x, y) = μ_H(u, v)`, and every `y ∈ C_v` has `μ_H(u, v) ≤ μ_G(x, y)` (no `sInf` on `ℕ`).
There is no forest hypothesis: the lemma holds for every strong metric generator. -/
theorem lemma_1 {VH VG : Type*} [Fintype VH] [Fintype VG]
    (H : SimpleGraph VH) (G : SimpleGraph VG) (hH : H.Connected) (hG : G.Connected)
    (T : Finset VH) (hT : IsStrongMetricGenerator H T) (f : ↥T → VG)
    (hf : IsIsometryOn H G T f) (C : VH → Set VG) (hC : Represents H G T f C) :
    ∀ u v : VH, ∀ x ∈ C u,
      (∃ y ∈ C v, G.dist x y = H.dist u v) ∧ (∀ y ∈ C v, H.dist u v ≤ G.dist x y) := by sorry

end MetricGenerators.IsometryExt
