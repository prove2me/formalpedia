-- Prove2me | Theorems.Thm_LowRandomnessDP_KNorm_lemma_4_5
-- name    : LowRandomnessDP.KNorm.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:06.665568+00:00
-- url     : https://prove2.me/theorems/6644ab02-5cb8-430c-8344-a94811e707f1
-- title:
--   Lemma 4.5 — cell entropy and actual logarithmic randomness
-- statement:
--   Fix $B\ge1$ in the MSSP envelope. For every sufficiently large fixed scale coefficient $S$, there are positive constants $C_H,C_b$ uniform over $d\ge2$, all admissible norms, $\varepsilon>0$, all MSSPs at scale $Sd/\varepsilon$ with that envelope, and all query values. For every input family $f:D\to\mathbb R^d$, the full cell law $p_x$ and an exact fair-bit sampler family $T_x$ for this same law satisfy
--
--   $$H_2(p_x)\le C_H\log d,\qquad
--   \sup_x\mathbb E[L_{T_x}]\le C_b\log d.$$
--
--   Mapping the sampled cell to its representative has exactly the Algorithm 2 output law. Both the entropy and actual randomness conclusions are present.
--
--   Differences from the source:
--   - encoding: real vectors and their K-norm → Fin d → ℝ with the Minkowski gauge of the exact compact convex symmetric absorbing disk; reason: coordinate encoding preserves all real vectors and all source norms; compactness excludes nontrivial linear subspaces
--   - generalization: finite datasets X* → an arbitrary dataset type D, with no adjacency hypothesis; reason: specializes to D=List X; entropy and sampling use neither adjacency nor input measurability
--   - encoding: probabilities and nonnegative expectations → ENNReal sums and mass-one PMFs, with finite positive normalizers proved in the conclusion; reason: retains divergent expectations as infinity and prevents divergent real sums from becoming zero
--   - encoding: the sufficiently large absolute Section 4 scale → for each fixed B≥1 a threshold S₀ and uniform constants for every fixed S≥S₀; reason: all constants precede dimension, norm, privacy parameter, partition and inputs; utility and entropy can use the same sufficiently large scale
--   - generalization: the chosen Theorem 3.2 partition and sensitivity-one queries → every MSSP with the same envelope and every query-value family; reason: entropy and sampling estimates do not use adjacency or sensitivity; the source instance is included
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf, Lemma 4.5, PDF page 17 / printed page 15

import Definitions.Def_LowRandomnessDP_KNorm_Sampling

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace LowRandomnessDP.KNorm

theorem lemma_4_5 :
    ∀ B : ℝ, 1 ≤ B → ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ S : ℝ, S₀ ≤ S →
      ∃ Ch Cb : ℝ, 0 < Ch ∧ 0 < Cb ∧
      ∀ (d : ℕ), 2 ≤ d → ∀ K : Set (Vec d), IsBody K →
      ∀ ε : ℝ, 0 < ε → ∀ (P : CellPartition d) (k : ℕ → ℕ),
      IsMSSP K P k (S * d / ε) → RateBound B d k →
      ∀ (D : Type) (f : D → Vec d),
        ∃ (p : D → PMF P.Cell) (T : D → DDG P.Cell),
          (∀ x c, p x c = gibbsMass ε (fun a => cellDistance K P a (f x)) c) ∧
          (∀ x, entropyBits (p x) ≤ ENNReal.ofReal (Ch * Real.log d)) ∧
          (∀ x, (T x).law = p x) ∧
          (∀ x, ((T x).law.map P.representative).toMeasure = expPart K P ε (f x)) ∧
          randomnessComplexity T ≤ ENNReal.ofReal (Cb * Real.log d) := by sorry

end LowRandomnessDP.KNorm
