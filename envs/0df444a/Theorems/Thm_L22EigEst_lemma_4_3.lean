-- Prove2me | Theorems.Thm_L22EigEst_lemma_4_3
-- name    : L22EigEst.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:21:41.947202+00:00
-- url     : https://prove2.me/theorems/51850a6a-2e58-4f51-b32e-d0cec6cc2f78
-- title:
--   Lemma 4.3 — event E1 (subspace embedding condition for $A'$) holds with probability $\ge0.95$
-- statement:
--   There is a constant $c_1>0$ such that the following holds. Let $A\in\mathbb R^{n\times n}$ be symmetric and non-zero, $\varepsilon\in(0,1/4)$, and let $s$ be an integer with $s\ge c_1\log(1/\varepsilon)/\varepsilon^2$ for which $A$ satisfies (1): $s\|A_i\|_2^2\le\|A\|_F^2$ for all $i$. Sample each row $i$ independently with probability $p_i=s\|A_i\|_2^2/\|A\|_F^2$ and let $S=\mathrm{diag}(\delta_i/\sqrt{p_i})$. Let $A'$ be the matrix of (2) and $L=\varepsilon\|A\|_F/200$. Then with probability at least $0.95$, event E1 holds:
--
--   $$\forall\lambda\ge L:\quad S\text{ is a }\min(L/\lambda,1/10)\text{-distortion subspace embedding of the span of the eigenvectors of }A'\text{ with eigenvalue of magnitude}\ge\lambda .$$
--
--   This is Lemma 4.3 of [SW25], quoted by the paper. E1 drives the eigenvalue comparison of Lemma 4.6.
--
--   Differences from the source:
--   - reading: the lemma's setting is stated once for §4 (p.13): A symmetric satisfying (1) for s, S drawn as in Algorithm 1 with p_i = s‖A_i‖₂²/‖A‖_F², A′ of (2), L = ε‖A‖_F/200 → these are explicit hypotheses and arguments of the statement, with the integer s universally quantified above the stated threshold; reason: the section's standing setting, written into the binders
--   - reading: Definition 4.2: "For ε ∈ (0, 1)" → ε ∈ (0, 1/4); reason: the events concern the sampling matrix of Algorithm 1, whose accuracy parameter is ε ∈ (0, 1/4) (Algorithm 1, Theorem 5); on (0, 1) Lemma 4.3 fails (A = I₂, ε close to 1, s = 1)
--   - encoding: S ∈ ℝ^{s×n} (or its n × n view) and E_S, Pr_S over the draw of S → the n × n diagonal view S_ii = δ_i/√p_i (sampMat), probabilities and expectations as finite sums over the 2ⁿ patterns δ (bernProb, bernExp); reason: the paper uses the two views interchangeably (p.9); a finite product of Bernoulli laws is exactly this sum
--   - encoding: A arbitrary in the setting of §4 → A ≠ 0; reason: p_i = s‖A_i‖₂²/‖A‖_F² is undefined (0/0) at A = 0; the proof of Theorem 4 removes zero rows (p.12)
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Lemma 4.3 and Definition 4.2 (Event E1), pp.13–14

import Definitions.Def_L22EigEst_BoundedRowNorm
import Definitions.Def_L22EigEst_bernW
import Definitions.Def_L22EigEst_sampMat
import Definitions.Def_L22EigEst_zeroed
import Definitions.Def_L22EigEst_SECond

namespace L22EigEst

/-- **Lemma 4.3** (Lemma 4.3 in [SW25], p.14), Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027
submission (manuscript sha256 b1f6adce…): "When s ≥ c1 log(1/ε)/ε² for some constant c1 > 0, event E1
occurs with probability at least 0.95." Event E1 (Definition 4.2, p.13): "For every λ ≥ L, the
sampling matrix S is a min(L/λ, 1/10)-distortion subspace embedding for the span of all
eigenvectors of A′ with eigenvalue of magnitude at least λ."

**Formalization Note (setting of §4, p.13).** `A` is symmetric and satisfies (1) for the integer
`s` (`BoundedRowNorm s A`); `S` is the sampling matrix of Algorithm 1 in the `n × n` view,
`sampMat p δ` with `p_i = s‖A_i‖₂²/‖A‖_F²` (`rowProb s A`) and `δ_i ∼ Ber(p_i)` independent;
probabilities and expectations over `δ` are finite sums (`bernProb`, `bernExp`); `A′ = zeroed A ε`;
`L = ε‖A‖_F/200`. `ε ∈ (0, 1/4)`, the domain of Algorithm 1, whose sampling matrix these events
are about.
`A ≠ 0` excludes the case where `p_i = s‖A_i‖₂²/‖A‖_F²` is undefined (`0/0`). -/
theorem lemma_4_3 :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (_hA : A.IsHermitian) (ε : ℝ)
      (s : ℕ), 0 < ε → ε < 1 / 4 → A ≠ 0 → c₁ * Real.log (1 / ε) / ε ^ 2 ≤ s →
      BoundedRowNorm s A →
      (0.95 : ℝ) ≤ bernProb (rowProb s A)
        (fun δ => SECond (zeroed A ε) (sampMat (rowProb s A) δ) (ε * frob A / 200)) := by sorry

end L22EigEst
