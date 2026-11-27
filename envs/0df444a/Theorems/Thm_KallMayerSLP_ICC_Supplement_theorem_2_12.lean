-- Prove2me | Theorems.Thm_KallMayerSLP_ICC_Supplement_theorem_2_12
-- name    : KallMayerSLP.ICC.Supplement.theorem_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:40:50.836442+00:00
-- url     : https://prove2.me/theorems/0575c992-175a-4dd7-910a-d943b76637f8
-- title:
--   Theorem 2.12 (Prékopa) — joint normal probability constraints with proportional covariance blocks are convex for $\alpha\ge\frac12$
-- statement:
--   Let $\xi$ be a random element with law $P$, and let $T(\xi)$ be a random $s\times n$ matrix and $h(\xi)\in\mathbb R^s$ a random vector. Write $\zeta^{(1)},\dots,\zeta^{(n+1)}$ for the columns of $(T(\xi),h(\xi))$ and $\eta^{(1)},\dots,\eta^{(s)}$ for its rows, let $C^{(i,j)}$ ($i,j=1,\dots,n+1$) be the $s\times s$ (cross-)covariance matrices of the columns and $\bar C^{(i,j)}$ ($i,j=1,\dots,s$) the $(n+1)\times(n+1)$ (cross-)covariance matrices of the rows. Assume that the vector $\zeta$ of all $s(n+1)$ entries of $(T(\xi),h(\xi))$ has a joint multivariate normal distribution (degenerate distributions allowed), and that
--
--   1. either there exist an $(n+1)\times(n+1)$ matrix $S$ and a symmetric positive semidefinite $s\times s$ matrix $C$ with $C^{(i,j)}=S_{ij}\,C$ for all $i,j$,
--   2. or there exist an $s\times s$ matrix $\bar S$ and a symmetric positive semidefinite $(n+1)\times(n+1)$ matrix $\bar C$ with $\bar C^{(i,j)}=\bar S_{ij}\,\bar C$ for all $i,j$.
--
--   Then, in both cases, for every $\alpha\ge\frac12$ the set
--   $$
--   \mathcal A(\alpha)=\{x\in\mathbb R^n\mid \mathbb P(T(\xi)x\le h(\xi))\ge\alpha\}
--   $$
--   is convex.
--
--   This is the main convexity result for joint probability constraints with a random technology matrix: without structure on the covariances, joint chance constraints with $s>1$ rows need not define convex feasible sets.
--
--   **Formalization Note** Joint normality is the book's Definition 2.1 (published as `KallMayerSLP.NormalCC.IsMultivariateNormal`) applied to the column-major vector of entries. The matrices $S$, $\bar S$ are arbitrary and $C$, $\bar C$ are positive semidefinite (`Matrix.PosSemidef`, which includes symmetry); no nonsingularity or positive definiteness is assumed. The two alternative hypotheses form one disjunction.
--
--   Differences from the source:
--   - generalization: ξ is a random vector, T(ξ), h(ξ) random (measurable) data of an s × n problem → Ξ any measurable space (in `Type`), P any probability measure on Ξ, T, h arbitrary functions (joint normality makes the entries a.e. equal to measurable functions), any s, n ∈ ℕ; reason: the hypotheses and the conclusion depend only on the joint law of the entries; Ξ = ℝʳ with P = ℙ_ξ and measurable T, h gives the book's case
--   - encoding: two alternative hypotheses "1 either … 2 or …" with the conclusion "in both cases" → one theorem whose covariance hypothesis is the disjunction of the two; reason: same instances, the conclusion is required under each alternative.
--   - encoding: covariances of normal entries → Mathlib's Bochner-integral `covariance` under the law $P$ of $\xi$; reason: normal entries are square integrable, so the values agree with the book's covariances.
--   - encoding: $\mathbb P(\zeta(x)\le 0)$ → `P.real` of the event that $T(\xi)x-h(\xi)\le0$ componentwise, with indices $0$-based; reason: Lean convention, same instances.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Theorem 2.12, p.139 (PDF 149); notation pp.137–138 (PDF 147–148); proof pp.139–141 (PDF 149–151)

import Mathlib
import Definitions.Def_KallMayerSLP_NormalCC_IsMultivariateNormal
import Definitions.Def_KallMayerSLP_ICC_Supplement_entryVec
import Definitions.Def_KallMayerSLP_ICC_Supplement_colCov
import Definitions.Def_KallMayerSLP_ICC_Supplement_rowCov
import Definitions.Def_KallMayerSLP_ICC_Supplement_setA

open Matrix MeasureTheory ProbabilityTheory

namespace KallMayerSLP.ICC.Supplement

/-- **Theorem 2.12 (Prékopa): joint normal probability constraints with proportional covariance
blocks are convex for `α ≥ ½`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, Theorem 2.12, p.139 (PDF 149):
"Let us assume that `ζ` has a joint multivariate normal distribution and that
1. either there exists an `((n + 1) × (n + 1))` matrix `S` and a symmetric positive semidefinite
   matrix `C`, such that `C^(i,j) = S_ij C` holds `∀ i, j`,
2. or there exists an `(s × s)` matrix `S̄` and a symmetric positive semidefinite matrix `C̄`, such
   that `C̄^(i,j) = S̄_ij C̄` holds, `∀ i, j`.
In both cases, if `α ≥ ½` then `𝒜(α)` is a convex set."

Here `ζ` is the vector of all `s(n+1)` entries of `(T(ξ), h(ξ))` (`entryVec`), `C^(i,j)` the
`s × s` (cross-)covariance blocks of the columns (`colCov`), `C̄^(i,j)` the `(n+1) × (n+1)`
(cross-)covariance blocks of the rows (`rowCov`), and `𝒜(α) = {x | ℙ(T(ξ)x ≤ h(ξ)) ≥ α}`
(`setA`).

**Formalization Note.** `P` is the law of `ξ` on `Ξ`. Joint normality is the book's
Definition 2.1 (the published `KallMayerSLP.NormalCC.IsMultivariateNormal`, degenerate normals
allowed) applied to the vector of entries. `S` and `S̄` are arbitrary real matrices and `C`, `C̄`
are symmetric positive semidefinite (`Matrix.PosSemidef`); no nonsingularity is assumed (the book
proves the case `S` nonsingular, resp. `C̄` positive definite, and cites Prékopa [234] for the
general case). The two alternatives are one disjunctive hypothesis. `α` is any real `≥ ½`. -/
theorem theorem_2_12 {Ξ : Type} [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]
    {s n : ℕ} (T : Ξ → Matrix (Fin s) (Fin n) ℝ) (h : Ξ → Fin s → ℝ)
    (hnormal : KallMayerSLP.NormalCC.IsMultivariateNormal P (entryVec T h))
    (hcov :
      (∃ (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (C : Matrix (Fin s) (Fin s) ℝ),
          C.PosSemidef ∧ ∀ i j, colCov P T h i j = S i j • C) ∨
      (∃ (Sbar : Matrix (Fin s) (Fin s) ℝ) (Cbar : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ),
          Cbar.PosSemidef ∧ ∀ i j, rowCov P T h i j = Sbar i j • Cbar))
    (α : ℝ) (hα : 1 / 2 ≤ α) :
    Convex ℝ (setA P T h α) := by sorry

end KallMayerSLP.ICC.Supplement
