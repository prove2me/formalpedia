-- Prove2me | Theorems.Thm_L22EigEst_lemma_4_11
-- name    : L22EigEst.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:23:01.033437+00:00
-- url     : https://prove2.me/theorems/d21f676c-3119-484b-ab7c-d14e99f66ce2
-- title:
--   Lemma 4.11 — $\big(\mathbb E_{S,S'}[\log(e+|S'|)\|SH_LS'^\top\|_{1\to2}^2]\big)^{1/2}\le\varepsilon\|A\|_F/(1600C_0)$
-- statement:
--   For every $C_0>0$ there is a constant $c_2>0$ such that the following holds. Let $A\in\mathbb R^{n\times n}$ be symmetric, $\varepsilon\in(0,1/4)$, and let $s$ be an integer with $s\ge c_2\log(1/\varepsilon)/\varepsilon^2$ for which $A$ satisfies (1). Let $S,S'$ be independent row-sampling matrices with $p_i=s\|A_i\|_2^2/\|A\|_F^2$, $A'$ the matrix of (2), $L=\varepsilon\|A\|_F/200$, $A'_L$ the part of $A'$ with eigenvalues of magnitude smaller than $L$, and $H_L$ the off-diagonal part of $A'_L$. Then
--
--   $$\Big(\mathbb E_{S,S'}\big[\log(e+|S'|)\cdot\|SH_LS'^\top\|_{1\to2}^2\big]\Big)^{1/2}\le\frac{\varepsilon\|A\|_F}{1600\,C_0}.$$
--
--   This controls the last term of (6) in Lemma 4.10 applied to $H_L$. It is where a union bound over all $n$ columns is replaced by one over the sampled columns only.
--
--   Differences from the source:
--   - reading: the lemma's setting is stated once for §4 (p.13): A symmetric satisfying (1) for s, S drawn as in Algorithm 1 with p_i = s‖A_i‖₂²/‖A‖_F², A′ of (2), L = ε‖A‖_F/200 → these are explicit hypotheses and arguments of the statement, with the integer s universally quantified above the stated threshold; reason: the section's standing setting, written into the binders
--   - reading: Definition 4.2: "For ε ∈ (0, 1)" → ε ∈ (0, 1/4); reason: the events concern the sampling matrix of Algorithm 1, whose accuracy parameter is ε ∈ (0, 1/4) (Algorithm 1, Theorem 5); on (0, 1) Lemma 4.3 fails (A = I₂, ε close to 1, s = 1)
--   - encoding: S ∈ ℝ^{s×n} (or its n × n view) and E_S, Pr_S over the draw of S → the n × n diagonal view S_ii = δ_i/√p_i (sampMat), probabilities and expectations as finite sums over the 2ⁿ patterns δ (bernProb, bernExp); reason: the paper uses the two views interchangeably (p.9); a finite product of Bernoulli laws is exactly this sum
--   - generalization: C0, the constant of Theorem 10 / Lemma 4.10 → every C₀ > 0, with c₂ depending on C₀; reason: the proof ends with "for sufficiently large choice of c2" (p.19), which works for any C₀ > 0; the paper's C₀ is one of them
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Lemma 4.11, p.17 (H_L defined on p.16)

import Definitions.Def_L22EigEst_BoundedRowNorm
import Definitions.Def_L22EigEst_bernW
import Definitions.Def_L22EigEst_sampMat
import Definitions.Def_L22EigEst_zeroed
import Definitions.Def_L22EigEst_highPart
import Definitions.Def_L22EigEst_colNorm12

namespace L22EigEst

/-- **Lemma 4.11** (p.17), Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027
submission (manuscript sha256 b1f6adce…): "For s ≥ c2 log(1/ε)/ε²,
(E_{S,S′}[log(e + |S′|) · ∥SH_L S′⊺∥²_{1→2}])^{1/2} ≤ ε∥A∥F/(1600C0)."
Here (p.16) "We split A′_L = D_L + H_L where D_L is a diagonal matrix and H_L is the off-diagonal
matrix of A′_L", and `C₀` is the constant of Lemma 4.10 / Theorem 10.

**Formalization Note (setting of §4, p.13).** `A` is symmetric and satisfies (1) for the integer
`s` (`BoundedRowNorm s A`); `S` is the sampling matrix of Algorithm 1 in the `n × n` view,
`sampMat p δ` with `p_i = s‖A_i‖₂²/‖A‖_F²` (`rowProb s A`) and `δ_i ∼ Ber(p_i)` independent;
probabilities and expectations over `δ` are finite sums (`bernProb`, `bernExp`); `A′ = zeroed A ε`;
`L = ε‖A‖_F/200`. `ε ∈ (0, 1/4)`, the domain of Algorithm 1, whose sampling matrix these events
are about.
`S′` is an independent copy (a second pattern `δ′`); the expectation is over the pair, then the
square root is taken. `H_L = offDiag (lowPart A′ L)`. The statement holds for every `C₀ > 0`, with
`c₂` depending on `C₀` only. -/
theorem lemma_4_11 :
    ∀ C₀ : ℝ, 0 < C₀ → ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
      (hA : A.IsHermitian) (ε : ℝ) (s : ℕ), 0 < ε → ε < 1 / 4 →
      c₂ * Real.log (1 / ε) / ε ^ 2 ≤ s → BoundedRowNorm s A →
      Real.sqrt (bernExp (rowProb s A) (fun δ => bernExp (rowProb s A) (fun δ' =>
          Real.log (Real.exp 1 + sampCount δ') *
            colNorm12 (sampMat (rowProb s A) δ *
              offDiag (lowPart (zeroed A ε) (zeroed_isHermitian hA ε) (ε * frob A / 200)) *
              sampMat (rowProb s A) δ') ^ 2))) ≤
        ε * frob A / (1600 * C₀) := by sorry

end L22EigEst
