-- Prove2me | Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_Supplement_density_concentration
-- name    : LinearHashingPoissonesque.ExpectedLoads.Supplement.density_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:08:49.969334+00:00
-- url     : https://prove2.me/theorems/038430d7-80a9-49d8-9919-bb13b225df82
-- title:
--   Theorem 10 (companion theorem; not used in the proof of the goal) — density concentration
-- statement:
--   Let $u\ge\ell\ge1$, $n=2^\ell$, $0<\varepsilon<1$, and $0<\rho<1$ with $\rho n\in\mathbb Z$. Let $A\subseteq\mathbb F_2^u$ have size $m$ and assume the strict inequality $m>n\log(1/\rho)$. For uniform linear $h:\mathbb F_2^u\to\mathbb F_2^\ell$,
--
--   $$\Pr_h\!\left[\forall B\subseteq\mathbb F_2^\ell,
--   \ |B|=\rho n\ \Longrightarrow\
--   \left|\Pr_{a\sim A}[h(a)\in B]-\rho\right|
--   \le5\rho\sqrt{\frac{n\log(1/\rho)}{\varepsilon m}}\right]\ge1-\varepsilon.$$
--
--   The inner probability is the fraction of elements of $A$ mapped into $B$. One event controls every $B$ of the prescribed density, on both sides of $\rho$.
--
--   Differences from the source:
--   - encoding: binary coordinate spaces and n = 2^ℓ → Fin u → ZMod 2 and Fin ℓ → ZMod 2, with n substituted as 2^ell; reason: these are exactly the source spaces and their cardinalities; ell is independent of the number of balls
--   - encoding: probability under a uniform random linear map → LinMaxLoad.probLin, the average of the event indicator over all linear maps; reason: the finite uniform law includes rank-deficient maps and imposes no surjectivity or affine shift
--   - encoding: a uniform element of A lands in B and rho*n is integral → the filtered cardinality divided by m, and ∃ k : ℕ, rho*2^ell = k; reason: A.card = m, the source hypotheses imply m > 0, and positive rho makes integer and natural witnesses equivalent
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.19, Theorem 10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf#page=19

import Definitions.Def_LinMaxLoad_probLin

namespace LinearHashingPoissonesque.ExpectedLoads.Supplement

/-- Theorem 10, p.19: simultaneous over every bin set with density rho. -/
theorem density_concentration {u ell m : ℕ} (hu : ell ≤ u) (hell : 1 ≤ ell)
    (A : Finset (Fin u → ZMod 2)) (hA : A.card = m)
    (eps rho : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1)
    (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hinteger : ∃ k : ℕ, rho * (2 : ℝ) ^ ell = k)
    (hdense : (2 : ℝ) ^ ell * Real.log (1 / rho) < m) :
    1 - eps ≤ LinMaxLoad.probLin (ZMod 2) (Fin u → ZMod 2) ell
      (fun h => ∀ B : Finset (Fin ell → ZMod 2),
        (B.card : ℝ) = rho * (2 : ℝ) ^ ell →
          |((A.filter (fun a => h a ∈ B)).card : ℝ) / m - rho| ≤
            5 * rho * Real.sqrt ((2 : ℝ) ^ ell * Real.log (1 / rho) / (eps * m))) := by sorry

end LinearHashingPoissonesque.ExpectedLoads.Supplement
