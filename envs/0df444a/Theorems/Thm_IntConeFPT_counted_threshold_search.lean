-- Prove2me | Theorems.Thm_IntConeFPT_counted_threshold_search
-- name    : IntConeFPT.counted_threshold_search
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-25T11:53:07.001715+00:00
-- url     : https://prove2.me/theorems/0048034b-a129-5828-9be1-23bbe413b801
-- title:
--   Witnessed search at one scaled integer objective threshold
-- statement:
--   For a counted instance of encoded length $L$, let $B=2^{L^2+4L}$ and let $q$ be the common cost denominator. Given a nonnegative index $k\le2B$, test the budget $(k-B)/q$. Either report that no feasible representation meets it, or return a rational sparse certificate meeting it with its correct aggregate. The test runs in the claimed FPT time in the counted input length, uniformly in these polynomial-bit indices. This isolates one budget test, rather than optimization. The intended algorithm is candidate enumeration (Corollaries 8, 10), rational lifts (Lemma 13), and blockwise recovery and duplicate merging (Lemma 6).
-- source:
--   Jansen, Ohnesorge and Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, https://arxiv.org/abs/2609.31328, §3.5, proof of Proposition 14, pp.16–17 (witnessed budget tests and binary search).

import Definitions.Def_IntConeFPT_Homogenized
import Definitions.Def_IntConeFPT_Machine
open OnlineCRS.Combine IntConeFPT

theorem IntConeFPT.counted_threshold_search :
    ∃ e : ℕ, ∃ A : Machine, ∀ I : Instance, I.Valid → ∀ N : ℕ,
      let x := encInstance I ++ encNat N ++ [3]
      let B := 2^(x.length^2 + 4*x.length)
      let q := ∏ t, ∏ j, (I.coeff t j).den
      ∀ k : ℕ, k ≤ 2*B → ∃ o : Output I,
        (match o with
         | .unbounded => False
         | .infeasible => ¬ ∃ μ, I.FeasibleN N μ ∧ (q : ℝ)*I.cost μ ≤ (k:ℝ)-B
         | .optimal y v cert => CertOK I cert ∧ I.FeasibleN N (certMult I cert) ∧
             I.totalAgg (certMult I cert) = ((fun i => (y i : ℝ)), fun i => (v i : ℝ)) ∧
             (q:ℝ)*I.cost (certMult I cert) ≤ (k:ℝ)-B) ∧
        RunsWithin A (x ++ encNat k ++ [3]) (encOutput o) (fptBound e I.τ I.d x.length) := by sorry
