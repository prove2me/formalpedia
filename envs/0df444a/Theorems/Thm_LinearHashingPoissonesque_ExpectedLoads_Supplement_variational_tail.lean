-- Prove2me | Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_Supplement_variational_tail
-- name    : LinearHashingPoissonesque.ExpectedLoads.Supplement.variational_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:05:51.491985+00:00
-- url     : https://prove2.me/theorems/f6d68364-9c26-432e-976f-ca87fc6dfe4b
-- title:
--   Corollary 2 (used in the proof of Theorem 9) — simultaneous variational tails
-- statement:
--   Let $u\ge\ell\ge1$, $m\ge1$, $n=2^\ell$ and $\mu=m/n$. Fix any $S\subseteq\mathbb F_2^u$ of size $m$ and $0<\varepsilon<1$. For a uniformly random linear $h:\mathbb F_2^u\to\mathbb F_2^\ell$, define
--
--   $$b_{\lambda,r}=\mu-\frac\mu\varepsilon+\frac{(\mu/\varepsilon)(e^\lambda-1)+\log(n/r)}\lambda.$$
--
--   For every $\lambda>0$ and, separately, every $\lambda<0$, respectively,
--
--   $$\Pr_h[\forall r\in[n]:L_r^+(S,h)<b_{\lambda,r}]\ge1-\varepsilon,\qquad
--   \Pr_h[\forall r\in[n]:L_r^-(S,h)>b_{\lambda,r}]\ge1-\varepsilon.$$
--
--   Each event is simultaneous over all $r$, at the fixed parameter $\lambda$. These are the variational tail bounds used by Theorem 9; the load inequalities are strict.
--
--   Differences from the source:
--   - encoding: binary coordinate spaces and n = 2^ℓ → Fin u → ZMod 2 and Fin ℓ → ZMod 2, with n substituted as 2^ell; reason: these are exactly the source spaces and their cardinalities; ell is independent of the number of balls
--   - encoding: probability under a uniform random linear map → LinMaxLoad.probLin, the average of the event indicator over all linear maps; reason: the finite uniform law includes rank-deficient maps and imposes no surjectivity or affine shift
--   - encoding: averages of the heaviest and lightest r labelled bins → published heaviestAverage and lightestAverage; reason: sorting all bin loads preserves every empty bin and every multiplicity
--   - encoding: each lambda of the indicated sign, with every r in [n] inside the event → two conjuncts quantified over positive and negative real lambda, with ∀ r, 1 ≤ r → r ≤ 2^ell inside each probLin; reason: both signs, strict inequalities and simultaneous r quantification are unchanged
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.13, Corollary 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf#page=13

import Definitions.Def_LinMaxLoad_probLin
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_ExtremeLoads

namespace LinearHashingPoissonesque.ExpectedLoads.Supplement

/-- Corollary 2, p.13: each event holds simultaneously for all valid r. -/
theorem variational_tail {u ell m : ℕ} (hu : ell ≤ u) (hell : 1 ≤ ell) (hm : 1 ≤ m)
    (S : Finset (Fin u → ZMod 2)) (hS : S.card = m)
    (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1) :
    let mu : ℝ := (m : ℝ) / (2 : ℝ) ^ ell
    (∀ lam : ℝ, 0 < lam →
      1 - eps ≤ LinMaxLoad.probLin (ZMod 2) (Fin u → ZMod 2) ell
        (fun h => ∀ r : ℕ, 1 ≤ r → r ≤ 2 ^ ell →
          heaviestAverage S h r < mu - mu / eps +
            (mu / eps * (Real.exp lam - 1) + Real.log ((2 : ℝ) ^ ell / r)) / lam)) ∧
    (∀ lam : ℝ, lam < 0 →
      1 - eps ≤ LinMaxLoad.probLin (ZMod 2) (Fin u → ZMod 2) ell
        (fun h => ∀ r : ℕ, 1 ≤ r → r ≤ 2 ^ ell →
          mu - mu / eps +
            (mu / eps * (Real.exp lam - 1) + Real.log ((2 : ℝ) ^ ell / r)) / lam <
          lightestAverage S h r)) := by sorry

end LinearHashingPoissonesque.ExpectedLoads.Supplement
