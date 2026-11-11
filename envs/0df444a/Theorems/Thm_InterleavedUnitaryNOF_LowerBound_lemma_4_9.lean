-- Prove2me | Theorems.Thm_InterleavedUnitaryNOF_LowerBound_lemma_4_9
-- name    : InterleavedUnitaryNOF.LowerBound.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:19.118718+00:00
-- url     : https://prove2.me/theorems/969c93f8-9e89-48db-b4ec-c94a44e4993b
-- title:
--   Lemma 4.9 — total sparse mass
-- statement:
--   Let $0<\epsilon\le10^{-4}$ and $d\ge8/\epsilon$. Consider supported measurable Boolean pairs $f_i,g_i$ on positive-measure boxes $B_i=\mathcal X_i\times\mathcal Y_i\times\mathcal Z_i$, a measurable Boolean factor $h$, and $c_i=f_ig_ih$. Use normalized local densities and assume $\sum_i\mu_0(B_i)\le4(d+3)^2$. Define $I_r=\{i:\delta_{f,i}>2^{-d},\ \delta_{g,i}>2^{-d},\ \delta_{h,i}>2^{-\epsilon d}\}$ and $I_s=[K]\setminus I_r$. There are universal constants $C,\kappa>0$ such that
--
--   $$\sum_{i\in I_s}\mu_1(c_i)\le Cd^2 2^{-\epsilon d/2}+|I_s|e^{-\kappa\sqrt m/2}.$$
--
--   In particular this bounds the total sparse mass in the source's regularity decomposition.
--
--   Differences from the source:
--   - encoding: positive matrix dimension and measurable Boolean functions on SU(m) powers → Fin m with NeZero m, normalized Borel Haar on the actual matrix group, and Bool indicators valued in ℝ; reason: these represent exactly the source objects, including m=1, without a discretization of the group
--   - encoding: sufficiently small positive ε and sufficiently large d in the p.13 preamble → 0<ε≤10⁻⁴ and d≥8/ε; reason: the proof fixes exactly this regime on pp.17–18; it is not imposed on the goal
--   - generalization: the sparse pieces of the regularity decomposition → any finite list of positive supported measurable boxes with the same volume bound and sparse index definition; reason: the p.18–19 estimate uses only Boolean factors, supports, normalized densities and total volume; the source list is included
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Lemma 4.9, printed p.13 = PDF p.13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Regularity

open MeasureTheory

namespace InterleavedUnitaryNOF.LowerBound

theorem lemma_4_9 : ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
    ∀ (m : ℕ) [NeZero m] (ε : ℝ), 0 < ε → ε ≤ (1 : ℝ)/10000 →
      ∀ (d : ℕ), 8/ε ≤ (d : ℝ) → ∀ (h : Quart m × Quart m → Bool),
      Measurable h → ∀ pieces : List (BoxPiece m),
      (∀ B ∈ pieces, B.Positive) →
      (pieces.map BoxPiece.volume).sum ≤ 4*((d : ℝ)+3)^2 →
      let sparse := Finset.univ \ regularIndices pieces h ε d
      (∑ i ∈ sparse, ∫ u, (pieces.get i).value h u ∂mu1 m) ≤
        C*(d : ℝ)^2 * Real.rpow 2 (-ε*d/2) +
        (sparse.card : ℝ)*Real.exp (-κ*Real.sqrt m/2) := by sorry

end InterleavedUnitaryNOF.LowerBound
