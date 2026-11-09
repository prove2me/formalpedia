-- Prove2me | Theorems.Thm_L22EigEst_claim_4_8
-- name    : L22EigEst.claim_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:27:03.030952+00:00
-- url     : https://prove2.me/theorems/ac635074-b570-4cc7-865c-7c5cae262faf
-- title:
--   Claim 4.8 — event E4 holds with probability $\ge0.95$ for $c$ large
-- statement:
--   There is $c_0$ such that for every $c\ge c_0$ the following holds. Let $A\in\mathbb R^{n\times n}$ be symmetric, $\varepsilon\in(0,1/4)$, $s=\lceil c\log(1/\varepsilon)/\varepsilon^2\rceil$, and suppose $A$ satisfies (1). Sample each row $i$ independently with probability $p_i=s\|A_i\|_2^2/\|A\|_F^2$, let $S=\mathrm{diag}(\delta_i/\sqrt{p_i})$, and let $A'$ be the matrix of (2). Then with probability at least $0.95$, event E4 holds:
--
--   $$\max_i\sum_{j\ne i}(SA'S^\top)_{ij}^2\le\frac{1000\,\varepsilon^2\|A\|_F^2}{c\log(1/\varepsilon)} .$$
--
--   The union bound runs only over the sampled rows, weighted by their probability $p_i$, so it costs a factor $\sum_ip_i=s$ rather than $n$.
--
--   Differences from the source:
--   - generalization: "If c is a sufficiently large constant" → every c ≥ c₀; reason: "sufficiently large" is a lower bound on c
--   - reading: the lemma's setting is stated once for §4 (p.13): A symmetric satisfying (1) for s, S drawn as in Algorithm 1 with p_i = s‖A_i‖₂²/‖A‖_F², A′ of (2), L = ε‖A‖_F/200 → these are explicit hypotheses and arguments of the statement, with the integer s universally quantified above the stated threshold; reason: the section's standing setting, written into the binders
--   - reading: Definition 4.2: "For ε ∈ (0, 1)" → ε ∈ (0, 1/4); reason: the events concern the sampling matrix of Algorithm 1, whose accuracy parameter is ε ∈ (0, 1/4) (Algorithm 1, Theorem 5); on (0, 1) Lemma 4.3 fails (A = I₂, ε close to 1, s = 1)
--   - encoding: S ∈ ℝ^{s×n} (or its n × n view) and E_S, Pr_S over the draw of S → the n × n diagonal view S_ii = δ_i/√p_i (sampMat), probabilities and expectations as finite sums over the 2ⁿ patterns δ (bernProb, bernExp); reason: the paper uses the two views interchangeably (p.9); a finite product of Bernoulli laws is exactly this sum
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Claim 4.8 and Definition 4.2 (Event E4), pp.14–15

import Definitions.Def_L22EigEst_BoundedRowNorm
import Definitions.Def_L22EigEst_bernW
import Definitions.Def_L22EigEst_eventE4

namespace L22EigEst

/-- **Claim 4.8** (p.15), Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027
submission (manuscript sha256 b1f6adce…): "If c is a sufficiently large constant, then event E4 occurs with probability at
least 0.95." Event E4 (Definition 4.2, p.14): "The off-diagonal parts of the row norms of the sampled
principal sub-matrix SA′S⊺ satisfy max_i Σ_{j≠i} (SA′S⊺)²_ij ≤ 1000 ε²∥A∥F²/(c log(1/ε))."

**Formalization Note.** `s = sParam c ε`, `δ_i ∼ Ber(p_i)` with `p_i = s‖A_i‖₂²/‖A‖_F²`
(`rowProb s A`), `A` symmetric with (1). Holds for every `c ≥ c₀`. `ε ∈ (0, 1/4)`, Algorithm 1's
domain. -/
theorem claim_4_8 :
    ∃ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (_hA : A.IsHermitian)
      (ε : ℝ), 0 < ε → ε < 1 / 4 → BoundedRowNorm (sParam c ε) A →
      (0.95 : ℝ) ≤ bernProb (rowProb (sParam c ε) A) (eventE4 c ε A) := by sorry

end L22EigEst
