-- Prove2me | Theorems.Thm_MaxCompForest_lemma_2_3
-- name    : MaxCompForest.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:37:42.399213+00:00
-- url     : https://prove2.me/theorems/b83ceda0-ee3d-463b-9449-cb651407fb86
-- title:
--   Lemma 2.3 — radius-frame bound
-- statement:
--   Let $x_v\in\mathbb R^d$, $d\ge1$, on the vertices of a finite loopless weighted graph with positive masses $w_v$. Suppose positive radii $r_v$ satisfy, for $\rho(u,v)=\|x_u-x_v\|$,
--   $$
--   |r_u-r_v|\le\rho(u,v),\qquad \sum_v w_v(r_v-\rho(c,v))_+^2\le T\ \text{ for every row }c .
--   $$
--   If $\lambda_{q+1}(N_W)\ge\gamma>0$ with $1\le q<n$, then
--   $$
--   S:=\sum_v w_vr_v^2\le3qT+\frac{328\,d\,\mathcal E(x)}{\gamma}.
--   $$
--   This is the key estimate: it bounds the sum of squared radii, and hence the assignment cost, by graph energy, with the center budget and the dimension contributing additively.
--
--   Differences from the source: none.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma 2.3, p.9

import Mathlib
import Definitions.Def_MaxCompForest_lam
import Definitions.Def_MaxCompForest_tent
import Definitions.Def_MaxCompForest_rowDist
import Definitions.Def_MaxCompForest_energy
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

/-- **Lemma 2.3 (Radius-frame bound)**, constant `328`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.9, under the standing assumptions of §2.1, p.7.

**Formalization Note.** `T` is any real for which (2.4) holds; (2.4) forces `T ≥ 0`. -/
theorem lemma_2_3 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (W : V → ℝ) (hW : ∀ v, 0 < W v) (q : ℕ) (hq1 : 1 ≤ q)
    (hqn : q < Fintype.card V) {d : ℕ} (hd : 1 ≤ d) (x : V → EuclideanSpace ℝ (Fin d))
    (r : V → ℝ) (hr : ∀ v, 0 < r v) (h23 : ∀ u v, |r u - r v| ≤ rowDist x u v) (T : ℝ)
    (h24 : ∀ c, ∑ v, W v * tent r (rowDist x) c v ^ 2 ≤ T) (γ : ℝ) (hγ : 0 < γ)
    (hlam : γ ≤ lam G W q) :
    ∑ v, W v * r v ^ 2 ≤ 3 * q * T + 328 * d * energy G x / γ := by sorry

end MaxCompForest
