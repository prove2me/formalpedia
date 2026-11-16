-- Prove2me | Theorems.Thm_LowRandomnessDP_KNorm_Supplement_lemma_3_6
-- name    : LowRandomnessDP.KNorm.Supplement.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:30:26.622477+00:00
-- url     : https://prove2.me/theorems/28e83bb4-b921-43c1-a596-c62e4b3f62b4
-- title:
--   Lemma 3.6 — small-ball image bound
-- statement:
--   There is an absolute real constant $c>0$ such that, for every $d\ge1$, every $x\in\mathbb R^d$ and every integer $1\le\ell\le d$, the image of the closed sup-norm ball under Algorithm 1 is finite and satisfies
--
--   $$\left|R\bigl(B_\infty(x;1/\ell)\bigr)\right|\le(\ell+1)^{c d/\ell}.$$
--
--   The same constant works for all dimensions, centres and scales. This is the small-ball image bound for the explicit partition.
--
--   Differences from the source:
--   - reading: $B_\infty(x;1/\ell)$ without an explicit boundary convention → the closed coordinate sup-norm ball; reason: the interval argument on PDF p. 13 covers the endpoints and agrees with the published partition interface
--   - encoding: cardinality at most $(\ell+1)^{O(d/\ell)}$ → explicit finiteness and real-cast `Set.ncard` bounded by a real power with one positive constant before $d,x,\ell$; reason: this expresses the absolute O bound and prevents infinite sets receiving cardinal zero
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), Lemma 3.6, PDF p. 13 / printed p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf; SHA-256 1562e70c55d785f992aaa32a161f0b06ac058da62f8f71fb07610037a20bc37b

import Definitions.Def_LowRandomnessDP_KNorm_Supplement_Rounding

set_option autoImplicit false

open Classical

namespace LowRandomnessDP.KNorm.Supplement

/-- Lemma 3.6, PDF 13 / printed 11. One absolute O constant, before all instances. -/
theorem lemma_3_6 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (hd : 0 < d) (x : Vec d)
      (ℓ : ℕ), 1 ≤ ℓ → ℓ ≤ d →
      (R hd '' infinityBall x (1 / (ℓ : ℝ))).Finite ∧
      ((R hd '' infinityBall x (1 / (ℓ : ℝ))).ncard : ℝ) ≤
        Real.rpow ((ℓ : ℝ) + 1) (c * (d : ℝ) / ℓ) := by sorry

end LowRandomnessDP.KNorm.Supplement
