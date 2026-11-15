-- Prove2me | Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_Supplement_failure_probability_lower_bound
-- name    : LinearHashingPoissonesque.ExpectedLoads.Supplement.failure_probability_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:10:43.296272+00:00
-- url     : https://prove2.me/theorems/0dcf32fa-71be-486b-bde3-8d02e144515b
-- title:
--   Theorem 11 (companion theorem; not used in the proof of the goal) — failure-probability lower bound
-- statement:
--   Let $m\ge n=2^\ell$ be powers of two, let $n/(88m)<\varepsilon<1/44$, and let $0<\rho\le1/2$ with $\rho n\in\mathbb Z$. There is a dimension threshold $U$, depending on $m,n,\varepsilon,\rho$, such that for every $u\ge U$ there is a set $A\subseteq\mathbb F_2^u$ of cardinality $m$ for which
--
--   $$\Pr_h\!\left[\exists B\subseteq\mathbb F_2^\ell:
--   |B|=\rho n\ \land\
--   \left|\Pr_{a\sim A}[h(a)\in B]-\rho\right|
--   \ge\frac\rho4\sqrt{\frac n{33\varepsilon m}}\right]\ge\varepsilon.$$
--
--   The outer probability is uniform over all linear maps. The bad set $A$ can depend on $u$, and the bin set $B$ can depend on the sampled map. This lower bound retains both non-strict conclusions and all four constants $88,44,4,33$.
--
--   Differences from the source:
--   - encoding: binary coordinate spaces and n = 2^ℓ → Fin u → ZMod 2 and Fin ℓ → ZMod 2, with n substituted as 2^ell; reason: these are exactly the source spaces and their cardinalities; ell is independent of the number of balls
--   - encoding: probability under a uniform random linear map → LinMaxLoad.probLin, the average of the event indicator over all linear maps; reason: the finite uniform law includes rank-deficient maps and imposes no surjectivity or affine shift
--   - encoding: powers of two m ≥ n=2^ell → exponents a,ell : ℕ with 2^ell ≤ 2^a and m substituted as 2^a; reason: every positive power-of-two size is represented; when ell=0 the density lattice with 0<rho≤1/2 has no instances
--   - encoding: a uniform element of A lands in B and rho*n is integral → the filtered cardinality divided by m, and ∃ k : ℕ, rho*2^ell = k; reason: A.card = m, the source hypotheses imply m > 0, and positive rho makes integer and natural witnesses equivalent
--   - encoding: for every sufficiently large u there is a set A → ∃ U, ∀ u ≥ U, ∃ A with A.card=2^a before probLin; reason: U is chosen after the source parameters, A can depend on u, and the event contains the existential B
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.21, Theorem 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf#page=21

import Definitions.Def_LinMaxLoad_probLin

namespace LinearHashingPoissonesque.ExpectedLoads.Supplement

/-- Theorem 11, p.21: for every sufficiently large universe dimension there is a bad A.
m = 2^a and n = 2^ell; rho*n is integral. -/
theorem failure_probability_lower_bound (a ell : ℕ) (hmn : 2 ^ ell ≤ 2 ^ a)
    (eps rho : ℝ)
    (heps0 : (2 : ℝ) ^ ell / (88 * (2 : ℝ) ^ a) < eps)
    (heps1 : eps < (1 : ℝ) / 44)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ (1 : ℝ) / 2)
    (hinteger : ∃ k : ℕ, rho * (2 : ℝ) ^ ell = k) :
    ∃ U : ℕ, ∀ u : ℕ, U ≤ u →
      ∃ A : Finset (Fin u → ZMod 2), A.card = 2 ^ a ∧
        eps ≤ LinMaxLoad.probLin (ZMod 2) (Fin u → ZMod 2) ell
          (fun h => ∃ B : Finset (Fin ell → ZMod 2),
            (B.card : ℝ) = rho * (2 : ℝ) ^ ell ∧
              (rho / 4) * Real.sqrt ((2 : ℝ) ^ ell / (33 * eps * (2 : ℝ) ^ a)) ≤
                |((A.filter (fun x => h x ∈ B)).card : ℝ) / (2 : ℝ) ^ a - rho|) := by sorry

end LinearHashingPoissonesque.ExpectedLoads.Supplement
