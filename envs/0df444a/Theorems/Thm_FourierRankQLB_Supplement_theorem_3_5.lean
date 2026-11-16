-- Prove2me | Theorems.Thm_FourierRankQLB_Supplement_theorem_3_5
-- name    : FourierRankQLB.Supplement.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:20:03.41264+00:00
-- url     : https://prove2.me/theorems/5fa80460-a81c-44a2-8354-0522b5fca7cb
-- title:
--   Theorem 3.5 — predicting $\det Q$ for Haar-random $Q$ with matrix phase queries needs $T \ge n/2$
-- statement:
--   Let $\mu_n$ be the normalized Haar measure on the orthogonal group $O(n)$. For $Q \in O(n)$ the **matrix phase oracle** (11) acts on query labels $(v,u) \in \mathbb R^n\times\mathbb R^n$ by $(P_Q\psi)(v,u) = e^{i u^\top Q v}\psi(v,u)$; one application of $P_Q$ or $P_Q^{-1}$ is one query.
--
--   **Theorem.** Consider a $T$-query algorithm that, given access to $P_Q$, outputs a prediction in $\{-1,+1\}$ of $\det Q$. If its success probability, averaged over $Q \sim \mu_n$, is strictly greater than $1/2$,
--
--   $$
--   \int_{O(n)} \Pr\big[\text{output} = \det Q\big]\, d\mu_n(Q) > \frac12,
--   $$
--
--   then
--
--   $$
--   T \ge \frac n2 .
--   $$
--
--   The bound is distributional: an algorithm with fewer than $n/2$ queries has Haar-average success exactly $1/2$, so it also fails on some $Q$. This is the paper's matrix-access lower bound; Theorem 3.9 reduces minimum-eigenvalue estimation to it.
--
--   **Formalization Note** The algorithm is the base mission's $T$-query algorithm (15) on the register $L^2(Y,\nu)\otimes W$ with a two-outcome POVM ($\mathrm{true}$ codes $+1$); each slot applies $P_Q$ or $P_Q^{-1}$ by a direction fixed with the algorithm. The circuit, the directions, the label space $(Y,\nu,\iota)$ and the POVM do not depend on $Q$.
--
--   Differences from the source:
--
--   - generalization: the register L²(ℝⁿ × ℝⁿ; ℂ) (Remark 3.6 / end of §6.1: also any finite label set with counting measure), with a workspace → L²(Y, ν) ⊗ W = L²(Y, ν; W) for any σ-finite (Y, ν), measurable labels ι : Y → ℝⁿ × ℝⁿ and any complex Hilbert space W; reason: covers more algorithms; Y = ℝⁿ × ℝⁿ with Lebesgue measure and ι = id gives L²(ℝⁿ × ℝⁿ; ℂ), and a finite label set with counting measure gives the remark's finite registers
--   - encoding: an algorithm that predicts det Q ∈ {−1, +1} → a POVM on Bool with boolSign true = +1, false = −1, succeeding on the outcome set {b | boolSign b = det Q}; reason: the base mission's published convention for ±1 predictions (Theorem 4.4); same algorithms
--   - encoding: one application of P_Q or P_Q^{-1} is one query → a direction vector inv : Fin T → Bool fixed with the algorithm; slot j applies P_Q (inv j = false) or P_Q.symm (inv j = true); reason: Lean representation of the paper's query model; same algorithms
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Theorem 3.5, p.20 (oracle Eq. (11), p.15; Remark 3.6, p.20)

import Mathlib
import Definitions.Def_FourierRankQLB_Supplement_matPhaseOracle
import Definitions.Def_FourierRankQLB_Supplement_dirOracles
import Definitions.Def_FourierRankQLB_QueryAlg_outcomeProb
import Definitions.Def_FourierRankQLB_boolSign
import Definitions.Def_FourierRankQLB_haarO

open MeasureTheory

namespace FourierRankQLB

namespace Supplement

/-- Theorem 3.5 (Continuous matrix phase determinant lower bound). Any algorithm which predicts
`det Q` for `Q ∼ μ_n` with average success probability strictly greater than `1/2`, using the
matrix phase oracle (11), makes at least `n/2` queries.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Theorem 3.5, p. 20 (oracle: Eq. (11), p. 15; finite label sets: Remark 3.6, p. 20).

**Formalization Note.** The algorithm is a `T`-query algorithm (15) on the register
`L²(Y, ν) ⊗ W`, for any σ-finite label space `(Y, ν)` whose labels `y` represent the query pairs
`ι y = (v, u) ∈ ℝⁿ × ℝⁿ` and any complex Hilbert workspace `W`; the paper's `L²(ℝⁿ × ℝⁿ)` is
`Y = ℝⁿ × ℝⁿ` with Lebesgue measure and `ι = id`, and Remark 3.6's finite label sets are counting
measures. Slot `j` applies `P_Q` or `P_Q⁻¹` according to `inv j`. The circuit, the directions, the
labels and the two-outcome POVM on `Bool` (`true` coding the prediction `+1`) are all fixed before
`Q`. -/
theorem theorem_3_5 {n : ℕ} {Y : Type} [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]
    (ι : Y → (Fin n → ℝ) × (Fin n → ℝ)) (hι : Measurable ι) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] (A : QueryAlg (Lp W 2 ν) Bool)
    (inv : Fin A.T → Bool)
    (hsucc : 1 / 2 < ∫ Q : Od n, A.outcomeProb
        (dirOracles (matPhaseOracle ν W ι hι (Q : Matrix (Fin n) (Fin n) ℝ)) inv)
        {b | boolSign b = (Q : Matrix (Fin n) (Fin n) ℝ).det} ∂haarO n) :
    (n : ℝ) / 2 ≤ A.T := by sorry

end Supplement

end FourierRankQLB
