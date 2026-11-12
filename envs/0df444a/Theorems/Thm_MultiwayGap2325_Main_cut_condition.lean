-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_cut_condition
-- name    : MultiwayGap2325.Main.cut_condition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-11T04:04:31.628059+00:00
-- url     : https://prove2.me/theorems/f87a7855-6a16-4174-975d-cc76bc18946b
-- title:
--   Lemma 5.1 — Cut condition
-- statement:
--   Let $r\ge2$, let $z\in\mathbb R^r$ have zero coordinate sum, and let $w_{ij}=w_{ji}\ge0$ for distinct indices. Suppose every nonempty proper subset $I$ satisfies
--   $$
--   \left|\sum_{i\in I}z_i\right|\le\sum_{i\in I,\ j\notin I}w_{ij}.
--   $$
--   Then for every $\nu\in\mathbb R^r$,
--   $$
--   \left|\sum_i\nu_i z_i\right|\le\sum_{i<j}w_{ij}|\nu_i-\nu_j|.
--   $$
--   This supplies the inequality for arbitrary interface normals from the coordinate-subset capacity constraints. Diagonal weights are unrestricted because neither side of a capacity sum uses them.
--
--   Differences from the source:
--   - encoding: the finite coordinate set S of a face → Fin r with r≥2; reason: enumerating the coordinate set changes neither subset sums nor the unordered-pair sum
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Lemma 5.1, p. 13

import Mathlib

namespace MultiwayGap2325.Main

/-- Lemma 5.1, p.13. Fin indices replace the finite ordered coordinate set S. -/
theorem cut_condition (r : ℕ) (hr : 2 ≤ r) (z : Fin r → ℝ) (w : Fin r → Fin r → ℝ)
    (hz : ∑ i, z i = 0)
    (hsym : ∀ i j, i ≠ j → w i j = w j i)
    (hnonneg : ∀ i j, i ≠ j → 0 ≤ w i j)
    (hcut : ∀ I : Finset (Fin r), I.Nonempty → I ≠ Finset.univ →
      |∑ i ∈ I, z i| ≤ ∑ i ∈ I, ∑ j ∈ Finset.univ \ I, w i j) :
    ∀ ν : Fin r → ℝ,
      |∑ i, ν i * z i| ≤ ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        w i j * |ν i - ν j| := by sorry

end MultiwayGap2325.Main
