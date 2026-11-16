-- Prove2me | Theorems.Thm_FourierRankQLB_Supplement_theorem_3_9
-- name    : FourierRankQLB.Supplement.theorem_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:20:45.921355+00:00
-- url     : https://prove2.me/theorems/6c6d60a5-f739-466b-b84a-a2e3e9f72efb
-- title:
--   Theorem 3.9 — estimating $\lambda_{\min}(S_Q)$ to accuracy $g_n/3$ with phase access to $S_Q$ needs $T \ge n/4$
-- statement:
--   Let $n$ be a positive even integer. For $Q \in O(n)$ let $S_Q = (Q+Q^\top)/2$ and let $\lambda_{\min}(S_Q)$ be its smallest eigenvalue. Put $\alpha = \pi/100$ and
--
--   $$
--   g_n = \frac{1-\cos(\alpha/n)}{2} = \Theta(n^{-2}) \qquad \text{(Eq. (25))}.
--   $$
--
--   The algorithm has matrix phase-oracle access to $S_Q$: on labels $(v,u)$, $(P_{S_Q}\psi)(v,u) = e^{i u^\top S_Q v}\psi(v,u)$, and one application of $P_{S_Q}$ or $P_{S_Q}^{-1}$ is one query.
--
--   **Theorem.** If a $T$-query algorithm with this access outputs, for every $Q \in O(n)$, an estimate $\tilde\lambda$ with
--
--   $$
--   \Pr\Big[\,|\tilde\lambda - \lambda_{\min}(S_Q)| \le \frac{g_n}{3}\,\Big] \ge \frac23,
--   $$
--
--   then
--
--   $$
--   T \ge \frac n4 .
--   $$
--
--   In particular, minimum-eigenvalue estimation needs $\Omega(n)$ queries at accuracy $\Theta(n^{-2})$. The result shows that high-accuracy spectral estimation in the phase model costs linearly many queries.
--
--   **Formalization Note** The model is that of Theorem 3.5 with the oracle of the matrix $S_Q$; the estimate is the outcome of a POVM on $\mathbb R$. $\lambda_{\min}$ is the published general definition `BlockBochner.lamMin` (the infimum of the real spectrum), which for the symmetric matrix $S_Q$ of positive size is its smallest eigenvalue. "Let $n$ be even" is taken with $n > 0$, since $\lambda_{\min}$ is undefined at $n = 0$.
--
--   Differences from the source:
--
--   - generalization: the register L²(ℝⁿ × ℝⁿ; ℂ) (Remark 3.6 / end of §6.1: also any finite label set with counting measure), with a workspace → L²(Y, ν) ⊗ W = L²(Y, ν; W) for any σ-finite (Y, ν), measurable labels ι : Y → ℝⁿ × ℝⁿ and any complex Hilbert space W; reason: covers more algorithms; Y = ℝⁿ × ℝⁿ with Lebesgue measure and ι = id gives L²(ℝⁿ × ℝⁿ; ℂ), and a finite label set with counting measure gives the remark's finite registers
--   - encoding: one application of P_{S_Q} or P_{S_Q}^{-1} is one query → a direction vector inv : Fin T → Bool fixed with the algorithm; slot j applies P_{S_Q} or its inverse; reason: Lean representation of the paper's query model; same algorithms
--   - reading: Let n be even → Even n and 0 < n; reason: λ_min(S_Q) has no meaning at n = 0 (no eigenvalues); the theorem is about matrices of positive even size
--   - reading: In particular, the task requires Ω(n) queries at accuracy Θ(n^{-2}) → not stated as a separate conjunct; reason: it restates T ≥ n/4 = Ω(n) together with g_n/3 = Θ(n^{-2}), a property of the constant g_n, and adds no claim about algorithms
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Theorem 3.9, p.22 (S_Q p.20; g_n Eq. (25), p.21; Remark 3.6, p.20)

import Mathlib
import Definitions.Def_FourierRankQLB_Supplement_matPhaseOracle
import Definitions.Def_FourierRankQLB_Supplement_dirOracles
import Definitions.Def_FourierRankQLB_Supplement_symPart
import Definitions.Def_BlockBochner_lamMin
import Definitions.Def_FourierRankQLB_QueryAlg_outcomeProb
import Definitions.Def_FourierRankQLB_gd

open MeasureTheory

namespace FourierRankQLB

namespace Supplement

/-- Theorem 3.9 (High-accuracy minimum-eigenvalue lower bound). Let `n` be even. Any algorithm with
matrix phase-oracle access to `S_Q = (Q + Qᵀ)/2` which, for every `Q ∈ O(n)`, estimates
`λ_min(S_Q)` to additive error at most `g_n/3` with success probability at least `2/3` makes at least
`n/4` queries.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Theorem 3.9, p. 22 (`S_Q`: p. 20; `g_n`: Eq. (25), p. 21; finite label sets: Remark 3.6, p. 20).

**Formalization Note.** "Let `n` be even" is read as a positive even `n` (`λ_min` needs `n ≥ 1`).
The oracle is the matrix phase oracle (11) of the matrix `S_Q`, on the register `L²(Y, ν) ⊗ W` for
any σ-finite label space and any workspace, as in Theorem 3.5; slot `j` applies `P_{S_Q}` or its
inverse according to `inv j`, fixed before `Q`. The estimate is the outcome of a POVM on `ℝ`.
`λ_min(S_Q)` is the published `BlockBochner.lamMin`, the infimum of the real spectrum, which for the
symmetric matrix `S_Q` of positive size is its smallest eigenvalue. The
sentence "In particular, the task requires `Ω(n)` queries at accuracy `Θ(n⁻²)`" restates `n/4 = Ω(n)`
and `g_n = Θ(n⁻²)` and is not stated separately. -/
theorem theorem_3_9 {n : ℕ} (hn : 0 < n) (heven : Even n) {Y : Type} [MeasurableSpace Y]
    (ν : Measure Y) [SigmaFinite ν] (ι : Y → (Fin n → ℝ) × (Fin n → ℝ)) (hι : Measurable ι)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (A : QueryAlg (Lp W 2 ν) ℝ) (inv : Fin A.T → Bool)
    (hsucc : ∀ Q : Od n, 2 / 3 ≤ A.outcomeProb (dirOracles (matPhaseOracle ν W ι hι (symPart Q)) inv)
        {e : ℝ | |e - BlockBochner.lamMin (symPart Q)| ≤ gd n / 3}) :
    (n : ℝ) / 4 ≤ A.T := by sorry

end Supplement

end FourierRankQLB
