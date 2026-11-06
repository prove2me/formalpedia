-- Prove2me | Theorems.Thm_FourierRankQLB_corollary_4_5
-- name    : FourierRankQLB.corollary_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:45:15.521847+00:00
-- url     : https://prove2.me/theorems/34bc4922-18e1-49b9-998f-96f17cedf00f
-- title:
--   Corollary 4.5 — continuous exact-membership determinant lower bound
-- statement:
--   Let $d\ge2$ be even, let $(Y,\nu)$ be a $\sigma$-finite query space, and let $q:Y\to\mathbb R^d$ and $\tau:Y\to\mathbb R$ be measurable. For each $Q\in O(d)$ define
--   $$
--   m_Q(y)=\mathbf 1[q(y)^TQq(y)\le\tau(y)].
--   $$
--   Any algorithm which predicts $\det Q$ for $Q\sim\mu_d$ with average success probability greater than $1/2$, using exact coherent query access to $m_Q$ on $L^2(Y,\nu)\otimes\mathbb C^2$, makes at least $d/2$ queries.
--
--   The main theorem uses this to cover continuous registers and query spaces that vary with the objective.
--
--   Differences from the source:
--
--   - generalization: the workspace $K$ is separable (standing assumption of Appendix A) → any complex Hilbert space `W`; reason: with $W_r$ the closed span of pure tensors, the printed proof does not use separability (a measurable $\Gamma$ is approximated on a countable partition of $Y$, uniformly in $Q$); separable workspaces are a special case
--   - encoding: $d$ of §4.2, the algorithm predicts $\det Q$ → hypotheses `2 ≤ d`, `Even d`; a POVM on `Bool`, `true` coding $+1$; reason: the values of $d_n$ for $n\ge2$; a two-outcome measurement is such a POVM
--   - encoding: each query slot an allowed query or inverse query, possibly controlled by the stored history, with identity padding (p.16) → every slot applies the membership oracle itself; reason: the oracle is an involution, so its inverse is itself; a controlled or identity slot is one plain query between Q-independent unitaries that swap the answer bit with a workspace qubit in the state $|+\rangle$, which the oracle fixes; the query count is unchanged
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Corollary 4.5, p.27, proved in Appendix A, p.50

import Mathlib
import Definitions.Def_FourierRankQLB_thresholdOracle
import Definitions.Def_FourierRankQLB_QueryAlg_outcomeProb
import Definitions.Def_FourierRankQLB_boolSign
import Definitions.Def_FourierRankQLB_haarO

open MeasureTheory

namespace FourierRankQLB

/-- Corollary 4.5 (Continuous exact-membership determinant lower bound). Let `(Y, ν)` be a σ-finite
query space, and `q : Y → ℝ^d`, `τ : Y → ℝ` measurable, with `m_Q(y) = 1[q(y)ᵀQq(y) ≤ τ(y)]`. Any
algorithm which predicts `det Q` for `Q ∼ μ_d` with average success probability greater than `1/2`,
using exact coherent query access to `m_Q` on `L²(Y, ν) ⊗ ℂ²`, makes at least `d/2` queries.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Corollary 4.5, p. 27, proved in Appendix A, p. 50.

**Formalization Note.** `d` is even and at least `2`. The algorithm has a workspace `W`, any complex
Hilbert space, and a two-outcome POVM on `Bool`, with `true` coding the prediction `+1`. -/
theorem corollary_4_5 {d : ℕ} (hd : 2 ≤ d) (hev : Even d) {Y : Type} [MeasurableSpace Y]
    (ν : Measure Y) [SigmaFinite ν] {q : Y → Fin d → ℝ} {τ : Y → ℝ} (hq : Measurable q)
    (hτ : Measurable τ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] (A : QueryAlg (QReg ν W) Bool)
    (hsucc : 1 / 2 < ∫ Q : Od d, A.outcomeProb (fun _ => thresholdOracle ν W hq hτ Q)
      {b | boolSign b = (Q : Matrix (Fin d) (Fin d) ℝ).det} ∂haarO d) :
    (d : ℝ) / 2 ≤ A.T := by sorry

end FourierRankQLB
