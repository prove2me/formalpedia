-- Prove2me | Theorems.Thm_HamLocality237_Testing_simulate_protocol
-- name    : HamLocality237.Testing.simulate_protocol
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:37:56.259699+00:00
-- url     : https://prove2.me/theorems/6ee6a72a-3102-4772-b590-62aace48e981
-- title:
--   §2.3.1 — uniform continuous-time simulation
-- statement:
--   Let $A$ be any finite adaptive $n$-qubit experiment protocol whose every branch costs at most $T$. For every $\delta>0$, there is one input-independent continuous-time algorithm $B$ with total cost at most $T$ such that, for every real diagonal table $h$ with $|h_x|\le1$,
--
--   $$|\Pr[A\text{ accepts }\operatorname{diag}(h)]-\Pr[B\text{ accepts }h]|\le\delta.$$
--
--   The same algorithm works for all bounded diagonal inputs. This transfers lower bounds from the continuous-time model to the source's adaptive experiments without increasing the charged evolution time.
--
--   Differences from the source:
--   - encoding: the finite-dimensional continuous-time model with a fixed unit basis state and final projective measurement → EuclideanSpace on Fin w × Qubits n, any unit initial vector, and a binary final orthogonal projection; reason: every unit vector can be selected as a basis vector; coarse-graining the final measurement gives the same binary acceptance law; finite-interval a.e. data can be extended by zero outside the interval
--   - generalization: the positive qubit count in the source model → the continuous-time statements also permit n=0; reason: the tensor and query sums retain one input site at n=0 and the dimension-independent argument applies; simulation at n=0 is input-independent and needs no query time
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), §2.3.1, pp.11–12. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Definitions.Def_HamLocality237_Testing_Dynamics

namespace HamLocality237.Testing

/-- §2.3.1: uniform simulation of every finite adaptive experiment tree. -/
theorem simulate_protocol (n : ℕ) (A : Protocol n) (T : ℝ)
    (hT : A.HasBranchTimeBound T) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ContinuousAlgorithm n, B.time ≤ T ∧
      ∀ h : QAlgorithms.Qubits n → ℝ, (∀ x, |h x| ≤ 1) →
        |A.acceptProbability (diagonalHamiltonian h) - B.acceptProbability h| ≤ δ := by sorry

end HamLocality237.Testing
