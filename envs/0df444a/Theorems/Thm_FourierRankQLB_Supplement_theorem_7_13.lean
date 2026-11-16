-- Prove2me | Theorems.Thm_FourierRankQLB_Supplement_theorem_7_13
-- name    : FourierRankQLB.Supplement.theorem_7_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:24:17.824713+00:00
-- url     : https://prove2.me/theorems/ec6431e2-dda5-48c4-8cd3-f3ebb52bd7af
-- title:
--   Theorem 7.13 — via inverse iteration: $C q/(\log(2+q)\log\log(3+q))$ gradient phase queries at accuracy $\rho^2/2$
-- statement:
--   Let $\rho = \sqrt{\sqrt{2c_\star} + c_\star^2}$ with $c_\star = 10^{-8}$ (Eq. (74)), and let $G_f$ be the ideal gradient phase oracle (58).
--
--   **Theorem.** There is a universal constant $C > 0$ such that the following holds for every $n \ge 1$ and $\kappa \ge 1$. Put $q := \min\{\sqrt\kappa, n\}$. There is a family $\mathcal F'_{n,\kappa}$ of quadratic functions on $\mathbb R^n$, each 1-strongly convex and κ-smooth, such that every quantum algorithm which, for every $f\in\mathcal F'_{n,\kappa}$, returns $\hat x$ with
--
--   $$
--   f(\hat x) \le \min_{x\in\mathbb R^n} f(x) + \frac{\rho^2}{2} \qquad (93)
--   $$
--
--   with probability at least $2/3$ makes at least
--
--   $$
--   C\,\frac{q}{\log(2+q)\,\log\log(3+q)} \qquad (94)
--   $$
--
--   gradient phase queries in the worst case. (The paper also names a universal constant $q_0$, which enters only the proof.)
--
--   This is the inverse-iteration version of Theorem 6.1, kept by the paper as a historical record of its first reduction: it loses a factor $\log q\log\log q$ and needs a smaller accuracy.
--
--   **Formalization Note** $C$ is chosen before $n$ and $\kappa$ and is uniform over all families and algorithms; $\log$ is the natural logarithm. The model is that of Theorem 6.1.
--
--   Differences from the source:
--
--   - generalization: the register L²(ℝⁿ × ℝⁿ) (Remark 3.6 / end of §6.1: also any finite label set with counting measure), with a workspace → L²(Y, ν) ⊗ W = L²(Y, ν; W) for any σ-finite (Y, ν), measurable labels ι : Y → ℝⁿ × ℝⁿ and any complex Hilbert space W; reason: covers more algorithms; Y = ℝⁿ × ℝⁿ with Lebesgue measure and ι = id gives L²(ℝⁿ × ℝⁿ), and a finite label set with counting measure gives the remark's finite registers
--   - encoding: one application of G_f or G_f^{-1} counts as one gradient query; "in the worst case" → a direction vector inv : Fin T → Bool fixed with the algorithm, and the bound on the number T of slots; reason: Lean representation of the paper's query model; the number of slots is the worst-case query count
--   - encoding: f(x̂) ≤ min_{x ∈ ℝⁿ} f(x) + ε → x̂ ∈ {x | ∀ z, f x ≤ f z + ε}; reason: equivalent, since every 1-strongly convex quadratic attains its minimum
--   - encoding: a quadratic function, 1-strongly convex and κ-smooth → IsSCSmoothQuadratic κ f: f = ½xᵀHx + bᵀx + c with H symmetric, (H − I) and (κI − H) positive semidefinite; reason: the paper's own definition on p.33 (I ⪯ H ⪯ κI)
--   - reading: There are universal constants C, q_0 > 0 such that … → ∃ C > 0, ∀ n ≥ 1, ∀ κ ≥ 1, …; q_0 is not quantified; reason: q_0 does not occur in the conclusion (94) or the hypotheses; it is a threshold of the proof only
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Theorem 7.13, p.46 (ρ Eq. (74), p.37; oracle Eq. (58), p.33)

import Mathlib
import Definitions.Def_FourierRankQLB_Supplement_gradPhaseOracle
import Definitions.Def_FourierRankQLB_Supplement_dirOracles
import Definitions.Def_FourierRankQLB_Supplement_IsSCSmoothQuadratic
import Definitions.Def_FourierRankQLB_Supplement_rhoStar
import Definitions.Def_FourierRankQLB_QueryAlg_outcomeProb

open MeasureTheory

namespace FourierRankQLB

namespace Supplement

/-- Theorem 7.13 (Gradient lower bound for strongly convex quadratics via inverse iteration). There
are universal constants `C, q₀ > 0` such that the following holds for every `n ≥ 1` and `κ ≥ 1`. Put
`q := min{√κ, n}`. There is an explicit family `F′_{n,κ}` of quadratic functions on `ℝⁿ`, each
1-strongly convex and κ-smooth, such that any quantum algorithm which, for every `f ∈ F′_{n,κ}`,
returns `x̂` satisfying `f(x̂) ≤ min_{x ∈ ℝⁿ} f(x) + ρ²/2` (93) with probability at least `2/3` makes at
least `C q/(log(2 + q) log log(3 + q))` (94) queries to the gradient phase oracle (58) in the worst case.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Theorem 7.13, p. 46 (`ρ`: Eq. (74), p. 37; oracle: Eq. (58), p. 33).

**Formalization Note.** `C` is chosen first and is uniform over all `n`, `κ`, families and
algorithms; `q₀` occurs only in the proof and is not part of the conclusion. `log` is the natural
logarithm. The model, the label spaces, the directions and the success event are as in Theorem 6.1,
with accuracy `ρ²/2`. -/
theorem theorem_7_13 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ κ : ℝ, 1 ≤ κ →
      ∃ F : Set (Ambient n → ℝ), (∀ f ∈ F, IsSCSmoothQuadratic κ f) ∧
        ∀ {Y : Type} [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]
          (ι : Y → Ambient n × Ambient n) (hι : Measurable ι)
          {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
          (A : QueryAlg (Lp W 2 ν) (Ambient n)) (inv : Fin A.T → Bool),
          (∀ f ∈ F, 2 / 3 ≤ A.outcomeProb (dirOracles (gradPhaseOracle ν W ι hι f) inv)
            {x | ∀ z, f x ≤ f z + rhoStar ^ 2 / 2}) →
          C * min (√κ) (n : ℝ) / (Real.log (2 + min (√κ) (n : ℝ)) *
            Real.log (Real.log (3 + min (√κ) (n : ℝ)))) ≤ A.T := by sorry

end Supplement

end FourierRankQLB
