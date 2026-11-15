-- Prove2me | Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_Supplement_density_concentration_intro
-- name    : LinearHashingPoissonesque.ExpectedLoads.Supplement.density_concentration_intro
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:09:24.042369+00:00
-- url     : https://prove2.me/theorems/8f487160-5788-493c-ac3e-b6159f35174d
-- title:
--   Theorem 6 (companion theorem; not used in the proof of the goal) — introductory density concentration
-- statement:
--   Let $u\ge\ell\ge1$ and $m\ge n=2^\ell$ be integers. Take $0<\varepsilon<1$ and $0<\rho\le1/2$ with $\rho n\in\mathbb Z$. For any $A\subseteq\mathbb F_2^u$ of size $m$, assume the non-strict inequality $m\ge n\log(1/\rho)$. A uniformly random linear map satisfies
--
--   $$\Pr_h\!\left[\forall B\subseteq\mathbb F_2^\ell,
--   \ |B|=\rho n\ \Longrightarrow\
--   \left|\Pr_{a\sim A}[h(a)\in B]-\rho\right|
--   \le5\rho\sqrt{\frac{n\log(1/\rho)}{\varepsilon m}}\right]\ge1-\varepsilon.$$
--
--   The statement retains the introductory theorem's own hypotheses, including the equality boundary in the density condition. Its simultaneous conclusion is the same form as Theorem 10's, under this different domain.
--
--   Differences from the source:
--   - encoding: binary coordinate spaces and n = 2^ℓ → Fin u → ZMod 2 and Fin ℓ → ZMod 2, with n substituted as 2^ell; reason: these are exactly the source spaces and their cardinalities; ell is independent of the number of balls
--   - encoding: probability under a uniform random linear map → LinMaxLoad.probLin, the average of the event indicator over all linear maps; reason: the finite uniform law includes rank-deficient maps and imposes no surjectivity or affine shift
--   - encoding: a uniform element of A lands in B and rho*n is integral → the filtered cardinality divided by m, and ∃ k : ℕ, rho*2^ell = k; reason: A.card = m, the source hypotheses imply m > 0, and positive rho makes integer and natural witnesses equivalent
--   - encoding: rho in (0,1/2] ∩ (1/n)ℤ → 0 < rho, rho ≤ 1/2 and a natural witness for rho*n; reason: with n=2^ell and rho>0 this is exactly the same density lattice; the printed non-strict density hypothesis is retained
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.6, Theorem 6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf#page=6

import Definitions.Def_LinMaxLoad_probLin

namespace LinearHashingPoissonesque.ExpectedLoads.Supplement

/-- Theorem 6, p.6: retain m ≥ n, rho ≤ 1/2, and the non-strict density condition. -/
theorem density_concentration_intro {u ell m : ℕ} (hu : ell ≤ u) (hell : 1 ≤ ell)
    (hmn : 2 ^ ell ≤ m) (A : Finset (Fin u → ZMod 2)) (hA : A.card = m)
    (eps rho : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ (1 : ℝ) / 2)
    (hinteger : ∃ k : ℕ, rho * (2 : ℝ) ^ ell = k)
    (hdense : (2 : ℝ) ^ ell * Real.log (1 / rho) ≤ m) :
    1 - eps ≤ LinMaxLoad.probLin (ZMod 2) (Fin u → ZMod 2) ell
      (fun h => ∀ B : Finset (Fin ell → ZMod 2),
        (B.card : ℝ) = rho * (2 : ℝ) ^ ell →
          |((A.filter (fun a => h a ∈ B)).card : ℝ) / m - rho| ≤
            5 * rho * Real.sqrt ((2 : ℝ) ^ ell * Real.log (1 / rho) / (eps * m))) := by sorry

end LinearHashingPoissonesque.ExpectedLoads.Supplement
