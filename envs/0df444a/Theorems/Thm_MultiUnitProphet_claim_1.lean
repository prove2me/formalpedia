-- Prove2me | Theorems.Thm_MultiUnitProphet_claim_1
-- name    : MultiUnitProphet.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:15.457991+00:00
-- url     : https://prove2.me/theorems/478ee667-53e2-48d8-bb77-59cc714bbebf
-- title:
--   Claim 1 — minimizing $\mu_k(X)$ over two biases is the (Min-Revenue) program
-- statement:
--   Let $k\ge1$, let $\bar X$ be a sum of independent Bernoullis with biases $b'\in[0,1]^m$, and let $X=\bar X+B_1+B_2$ with independent $B_i\sim\mathrm{Bernoulli}(1-r_i)$, $r_1,r_2\in[0,1]$. With $Q_1=\mathbb P[\bar X=k-1]$, $Q_2=\mathbb P[\bar X=k-2]$, $Q_{\ge3}=\mathbb P[\bar X\le k-3]$:
--
--   1. $\delta_k(X)=Q_{\ge3}+Q_2(r_1+r_2-r_1r_2)+Q_1r_1r_2$;
--   2. $k\,\mu_k(X)=k\,\mu_k(\bar X)+(Q_1+2Q_2+2Q_{\ge3})-\big[(Q_2+Q_{\ge3})(r_1+r_2)+Q_1r_1r_2\big]$;
--   3. for every constant $\phi$, $\delta_k(X)=\phi$ iff $(r_1,r_2)$ satisfies (5.1): $r_1r_2(Q_1-Q_2)+(r_1+r_2)Q_2=\phi-Q_{\ge3}$;
--   4. for two points $(r_1,r_2)$ and $s$ satisfying (5.1), $\mu_k$ is smaller at $(r_1,r_2)$ iff the (Min-Revenue) objective $(Q_2+Q_{\ge3})(r_1+r_2)+Q_1r_1r_2$ is larger there.
--
--   So minimizing $\mu_k(X)$ in $(r_1,r_2)$ subject to $\delta_k(X)=\phi^\star_k$ is the (Min-Revenue) program.
--
--   Differences from the source:
--   - encoding: a supply k (a positive integer) → k : ℕ with 1 ≤ k; reason: the supply is a positive number of units; at k = 0 the quantities are degenerate
--   - reading: is captured by the following program → the two identities for δ_k(X) and k µ_k(X) and the resulting equivalences of the constraint and of the order of objective values; reason: these are exactly what the proof of Claim 1 establishes and what 'captured' means for the minimization
--   - generalization: the constant value φ⋆_k → every real constant φ; reason: φ⋆_k is one value of φ
--   - encoding: X̄ the sum of the remaining n − 2 distributions → X̄ with m arbitrary Bernoullis (m = n − 2), X with bias vector Fin.append b' ![1 − r_1, 1 − r_2]; reason: Lean indexing of the n biases
--   - encoding: X a sum of independent Bernoullis with biases b_t → deltaPB k b and muPB k b, finite sums over the pmf CommitteeVoting.SingleVoter.pbPMF b univ j, with b t ∈ [0, 1]; reason: the Poisson-binomial law written through its pmf; same values
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, Claim 1, p.12 (proof pp.12–13)

import Mathlib
import Definitions.Def_MultiUnitProphet_PoissonBinomial
import Definitions.Def_MultiUnitProphet_MinRevenue

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MultiUnitProphet

/-- **Claim 1: minimizing `µ_k(X)` over two biases is the (Min-Revenue) program.**
Chawla, Devanur & Lykouris, *Static pricing for multi-unit prophet inequalities*,
arXiv:2007.07990v4, Claim 1, p.12 (proof pp.12–13): "The problem of minimizing µk(X) as a function of r1 and
r2 subject to δk(X) = ϕ⋆k for a constant value ϕ⋆k is captured by the following program:
Maximize (Q2 + Q≥3)·(r1 + r2) + Q1r1r2 subject to r1, r2 ∈ [0, 1]² and
r1r2·(Q1 − Q2) + (r1 + r2)·Q2 = ϕ⋆k − Q≥3 (5.1)."

Let `X̄` be the sum of `m` independent Bernoullis with biases `b'`, `X = X̄ + B_1 + B_2` with
`B_i` Bernoulli of bias `1 − r_i`, `Q_1 = P[X̄ = k − 1]`, `Q_2 = P[X̄ = k − 2]`,
`Q_{≥3} = P[X̄ ≤ k − 3]`. Then
1. `δ_k(X) = Q_{≥3} + Q_2 (r_1 + r_2 − r_1 r_2) + Q_1 r_1 r_2` (p.12);
2. `k µ_k(X) = k µ_k(X̄) + (Q_1 + 2Q_2 + 2Q_{≥3}) − [(Q_2 + Q_{≥3})(r_1 + r_2) + Q_1 r_1 r_2]` (p.13);
3. for every constant `φ` and `(r_1, r_2) ∈ [0,1]²`, `δ_k(X) = φ` iff `(r_1, r_2)` satisfies (5.1);
4. among `(r_1, r_2)` satisfying (5.1), `µ_k(X)` is smaller exactly when the (Min-Revenue)
   objective is larger.

**Formalization Note.** The constant value `φ` is arbitrary (the paper's `φ⋆_k` is one value).
The bias vector of `X` is `Fin.append b' ![1 − r_1, 1 − r_2]` on `Fin (m + 2)`. -/
theorem claim_1 (k m : ℕ) (hk : 1 ≤ k) (b' : Fin m → ℝ) (hb' : ∀ t, b' t ∈ Set.Icc (0 : ℝ) 1)
    (r1 r2 : ℝ) (hr1 : r1 ∈ Set.Icc (0 : ℝ) 1) (hr2 : r2 ∈ Set.Icc (0 : ℝ) 1) :
    deltaPB k (twoBiasExtend b' r1 r2) =
        Qge3 k b' + Qtwo k b' * (r1 + r2 - r1 * r2) + Qone k b' * r1 * r2 ∧
    (k : ℝ) * muPB k (twoBiasExtend b' r1 r2) =
        (k : ℝ) * muPB k b' + (Qone k b' + 2 * Qtwo k b' + 2 * Qge3 k b')
          - minRevObj (Qone k b') (Qtwo k b') (Qge3 k b') (r1, r2) ∧
    (∀ φ : ℝ, deltaPB k (twoBiasExtend b' r1 r2) = φ ↔
        (r1, r2) ∈ minRevFeasible (Qone k b') (Qtwo k b') (Qge3 k b') φ) ∧
    (∀ φ : ℝ, ∀ s : ℝ × ℝ,
        (r1, r2) ∈ minRevFeasible (Qone k b') (Qtwo k b') (Qge3 k b') φ →
        s ∈ minRevFeasible (Qone k b') (Qtwo k b') (Qge3 k b') φ →
        (muPB k (twoBiasExtend b' r1 r2) ≤ muPB k (twoBiasExtend b' s.1 s.2) ↔
          minRevObj (Qone k b') (Qtwo k b') (Qge3 k b') s ≤
            minRevObj (Qone k b') (Qtwo k b') (Qge3 k b') (r1, r2))) := by sorry

end MultiUnitProphet
