-- Prove2me | Theorems.Thm_L22EigEst_lemma_4_4
-- name    : L22EigEst.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:21:58.402834+00:00
-- url     : https://prove2.me/theorems/9e61a1a9-5dce-40ed-8cab-75173ba58816
-- title:
--   Lemma 4.4 — event E2, $\|SA'_LS^\top\|_2\le\varepsilon\|A\|_F$, holds with probability $\ge0.95$
-- statement:
--   There is a constant $c_2>0$ such that the following holds. Let $A\in\mathbb R^{n\times n}$ be symmetric, $\varepsilon\in(0,1/4)$, and let $s$ be an integer with $s\ge c_2\log(1/\varepsilon)/\varepsilon^2$ for which $A$ satisfies (1). Let $S$ be the row-sampling matrix with $p_i=s\|A_i\|_2^2/\|A\|_F^2$, $A'$ the matrix of (2), $L=\varepsilon\|A\|_F/200$, and $A'_L$ the part of $A'$ with eigenvalues of magnitude smaller than $L$ (Definition 2.3). Then with probability at least $0.95$, event E2 holds:
--
--   $$\|SA'_LS^\top\|_2\le\varepsilon\|A\|_F ,$$
--
--   where $\|\cdot\|_2$ is the spectral norm.
--
--   Removing the $\operatorname{polylog}(n)$ factor that earlier versions of this bound needed in $s$ is one of the paper's contributions.
--
--   Differences from the source:
--   - reading: the lemma's setting is stated once for §4 (p.13): A symmetric satisfying (1) for s, S drawn as in Algorithm 1 with p_i = s‖A_i‖₂²/‖A‖_F², A′ of (2), L = ε‖A‖_F/200 → these are explicit hypotheses and arguments of the statement, with the integer s universally quantified above the stated threshold; reason: the section's standing setting, written into the binders
--   - reading: Definition 4.2: "For ε ∈ (0, 1)" → ε ∈ (0, 1/4); reason: the events concern the sampling matrix of Algorithm 1, whose accuracy parameter is ε ∈ (0, 1/4) (Algorithm 1, Theorem 5); on (0, 1) Lemma 4.3 fails (A = I₂, ε close to 1, s = 1)
--   - encoding: S ∈ ℝ^{s×n} (or its n × n view) and E_S, Pr_S over the draw of S → the n × n diagonal view S_ii = δ_i/√p_i (sampMat), probabilities and expectations as finite sums over the 2ⁿ patterns δ (bernProb, bernExp); reason: the paper uses the two views interchangeably (p.9); a finite product of Bernoulli laws is exactly this sum
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Lemma 4.4 and Definition 4.2 (Event E2), pp.13–14

import Definitions.Def_L22EigEst_BoundedRowNorm
import Definitions.Def_L22EigEst_bernW
import Definitions.Def_L22EigEst_sampMat
import Definitions.Def_L22EigEst_zeroed
import Definitions.Def_L22EigEst_highPart
import Definitions.Def_WainwrightHDS_EigPert_opNorm2

open WainwrightHDS.EigPert

namespace L22EigEst

/-- **Lemma 4.4** (p.14), Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027
submission (manuscript sha256 b1f6adce…): "When s ≥ c2 log(1/ε)/ε² for some constant c2 > 0, event E2 occurs with
probability at least 0.95." Event E2 (Definition 4.2, p.13): "The sampled matrix satisfies
∥SA′_L S⊺∥2 ≤ ε∥A∥F", with `A′_L` the small-eigenvalue part of `A′` at threshold `L` (Definition 2.3).

**Formalization Note (setting of §4, p.13).** `A` is symmetric and satisfies (1) for the integer
`s` (`BoundedRowNorm s A`); `S` is the sampling matrix of Algorithm 1 in the `n × n` view,
`sampMat p δ` with `p_i = s‖A_i‖₂²/‖A‖_F²` (`rowProb s A`) and `δ_i ∼ Ber(p_i)` independent;
probabilities and expectations over `δ` are finite sums (`bernProb`, `bernExp`); `A′ = zeroed A ε`;
`L = ε‖A‖_F/200`. `ε ∈ (0, 1/4)`, the domain of Algorithm 1, whose sampling matrix these events
are about.
`‖·‖₂` is the spectral norm `opNorm2`. -/
theorem lemma_4_4 :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (ε : ℝ)
      (s : ℕ), 0 < ε → ε < 1 / 4 → c₂ * Real.log (1 / ε) / ε ^ 2 ≤ s → BoundedRowNorm s A →
      (0.95 : ℝ) ≤ bernProb (rowProb s A)
        (fun δ => opNorm2 (sampMat (rowProb s A) δ *
            lowPart (zeroed A ε) (zeroed_isHermitian hA ε) (ε * frob A / 200) *
            sampMat (rowProb s A) δ) ≤ ε * frob A) := by sorry

end L22EigEst
