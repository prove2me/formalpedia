-- Prove2me | Theorems.Thm_NNPartTree_claim_5_7
-- name    : NNPartTree.claim_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:41.834003+00:00
-- url     : https://prove2.me/theorems/ca9f47c0-3236-4bf6-b8db-9b737485e47b
-- title:
--   Claim 5.7, p.19 — $\zeta\sim N(0,M)$ gives $R_S(A_\zeta)\le cB$ and $\gamma(A_\zeta;S_Y)\le cC$ with probability $1/8$
-- statement:
--   There is an absolute constant $c$ such that the following holds. Fix a sample $S$ of $m\ge1$ pairs, $C>1$, and a matrix $M$ feasible for $\Pi_{\mathrm{sdp}}(S,C)$ with objective value at most $B$. If $\zeta\sim N(0,M)$, then with probability at least $1/8$ the polynomial $A_\zeta(x)=\zeta^\top\phi_k(x)$ has positive variance on $S_Y$ and
--   $$R_S(A_\zeta)\le cB\quad\text{and}\quad\gamma(A_\zeta;S_Y)\le cC.$$
--
--   Substituting $C=500c'/\beta^2$ and $B=O(1/\beta)(\mathrm{OPT}_\beta(\mathcal F)+\varepsilon)$ gives the printed form. This rounds the semidefinite solution to an actual polynomial.
--
--   Differences from the source:
--   - generalization: M satisfying the conclusions of Claim 5.6 → any M feasible for Π_sdp(S, C) with objective at most B; reason: the proof uses only feasibility and the objective value; the printed M is the case C = 500c/β²
--   - encoding: with probability 1/8 → failure set has outer measure at most 7/8; positive variance included in the event; reason: R and γ are 0 in Lean on zero variance, and the proof gives s₂ > 1/10
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Claim 5.7, p.19; proof pp.19–20

import Mathlib
import Definitions.Def_NNPartTree_Learner

open MeasureTheory ProbabilityTheory

namespace NNPartTree

/-- **Claim 5.7**, p.19; proof pp.19–20. S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…).

Fix a sample `S` and a psd `M` feasible for `Π_sdp(S, C)` with objective at most `B`. If `ζ ∼ N(0, M)`, then with
probability at least `1/8` the polynomial `A_ζ(x) = ζ^⊤ φ_k(x)` has positive variance on `S_Y`,
`R_S(A_ζ) ≤ c B` and `γ(A_ζ; S_Y) ≤ c C`, with `c` absolute.

**Formalization Note.** Substituting `C = 500c/β²` and `B = O(1/β)(OPT_β(F) + ε)` gives the printed form. The
probability is written as failure at most `7/8`. Positive variance is included because `R` and `γ` are `0` in Lean
on zero variance. `N(0, M)` is Mathlib's `multivariateGaussian`. -/
theorem claim_5_7 : ∃ c : ℝ, 0 < c ∧ ∀ (d k m : ℕ) (S : Fin m → Pt d × Pt d)
    (C B : ℝ) (M : Matrix (Fin (numMonomials d k)) (Fin (numMonomials d k)) ℝ),
    1 ≤ m → 1 < C → SdpFeasible S C M → sdpObjective S M ≤ B →
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin (numMonomials d k))) M
        {ζ | ¬ (0 < varOn (marginalY (empirical S)) (evalCoef (k := k) fun a => ζ a) ∧
          energy (empirical S) (evalCoef (k := k) fun a => ζ a) ≤ c * B ∧
          kurtosis (marginalY (empirical S)) (evalCoef (k := k) fun a => ζ a) ≤ c * C)} ≤
      ENNReal.ofReal (7 / 8) := by sorry

end NNPartTree
