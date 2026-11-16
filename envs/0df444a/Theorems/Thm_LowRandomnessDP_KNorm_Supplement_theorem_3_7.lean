-- Prove2me | Theorems.Thm_LowRandomnessDP_KNorm_Supplement_theorem_3_7
-- name    : LowRandomnessDP.KNorm.Supplement.theorem_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:30:58.029692+00:00
-- url     : https://prove2.me/theorems/22560ce2-df6e-48fe-a7b0-040ea77f8d8a
-- title:
--   Theorem 3.7 — explicit infinity-norm MSSP
-- statement:
--   There is an absolute real constant $c>0$ such that, for every $d\ge1$, the particular partition induced by Algorithm 1, with each rounded output as its representative, is a multi-scale secluded partition at radius $\rho=1$. More precisely, there is a positive integer bound $k_d(\ell)$ at every integer scale $1\le\ell\le d$ such that every closed sup-norm ball of radius $1/\ell$ meets at most $k_d(\ell)$ cells, all points are within sup-norm distance one of their cell representative, and
--
--   $$k_d(\ell)\le(\ell+1)^{c d/\ell}.$$
--
--   This is a companion theorem. It specifies the explicit partition simultaneously at every scale; it is not used in the proof of the mission's goal Theorem 4.1.
--
--   Differences from the source:
--   - reading: secludedness using norm balls without an explicit boundary convention → the published `IsMSSP` counts cells meeting closed balls; reason: the counting argument covers closed balls, including boundary points
--   - encoding: a $k_d$-MSSP for some radius with $k_d(\ell)=(\ell+1)^{O(d/\ell)}$ → the concrete Algorithm 1 `CellPartition`, radius one, and natural-valued $k$ bounded by a real power with one absolute positive constant before $d$; reason: Lemma 3.3 and Lemma 3.6 give radius one and the uniform rate for this same partition; the source omits its radius
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), Theorem 3.7, PDF p. 13 / printed p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf; SHA-256 1562e70c55d785f992aaa32a161f0b06ac058da62f8f71fb07610037a20bc37b

import Definitions.Def_LowRandomnessDP_KNorm_Supplement_Rounding

set_option autoImplicit false

open Classical

namespace LowRandomnessDP.KNorm.Supplement

/-- Theorem 3.7, PDF 13 / printed 11: THIS Algorithm 1 partition, at scale one. -/
theorem theorem_3_7 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (hd : 0 < d), ∃ k : ℕ → ℕ,
      IsMSSP (infinityBody d) (inducedPartition hd) k 1 ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ d →
        (k ℓ : ℝ) ≤ Real.rpow ((ℓ : ℝ) + 1) (c * (d : ℝ) / ℓ) := by sorry

end LowRandomnessDP.KNorm.Supplement
