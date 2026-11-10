-- Prove2me | Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_variational_expectation
-- name    : LinearHashingPoissonesque.ExpectedLoads.variational_expectation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T19:02:54.082445+00:00
-- url     : https://prove2.me/theorems/8a82b1ce-afdd-4601-ac67-4e399503fe6f
-- title:
--   Corollary 1 — two-sided variational bounds for both signs
-- statement:
--   Let $u\ge\ell\ge1$, $m\ge1$, $n=2^\ell$, $1\le r\le n$, and $\mu=m/n$. Fix $S\subseteq\mathbb F_2^u$ with $|S|=m$, and sample $h:\mathbb F_2^u\to\mathbb F_2^\ell$ uniformly from all linear maps. For each $\star\in\{-,+\}$,
--
--   $$\sup_{\lambda<0}\frac{\mu(e^\lambda-1)+\log(n/r)}{\lambda}\ \le\ \mathbb E_h[L_r^\star(S,h)]\ \le\ \inf_{\lambda>0}\frac{\mu(e^\lambda-1)+\log(n/r)}{\lambda}.$$
--
--   Both inequalities hold for both extreme averages. The sign domains are strict, so no division by zero occurs. The real supremum and infimum are retained without requiring that an optimizing parameter exists, including when $r=n$.
--
--   Differences from the source:
--   - encoding: binary coordinate spaces, n = 2^ℓ and μ = m/n → Fin u → ZMod 2 and Fin ℓ → ZMod 2, with n and μ substituted in the formulas; reason: these coordinate spaces have exactly the source cardinalities, and ℓ is independent of m
--   - encoding: expectation under the uniform law on all linear maps → LinMaxLoad.avgLin, a finite sum divided by the number of all linear maps; reason: the published definition includes singular maps and introduces no conditioning or regularity assumptions
--   - encoding: supremum over λ < 0 and infimum over λ > 0 → real sSup and sInf of the corresponding value images, named variationalLower and variationalUpper; reason: the local analytic verification proves the images nonempty and bounded on the required side; no boundedness hypothesis is added
--   - encoding: two inequalities for either sign → a conjunction parameterized by Extreme; reason: both clauses are present for each of the two sign values
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.13, Corollary 1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf

import Definitions.Def_LinMaxLoad_avgLin
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_LogPotential
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_ExtremeLoads
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_VariationalBounds

namespace LinearHashingPoissonesque.ExpectedLoads

/-- Corollary 1, p.13: both inequalities for each of the two extreme averages. -/
theorem variational_expectation {u ell m : ℕ} (hu : ell ≤ u) (hell : 1 ≤ ell) (hm : 1 ≤ m)
    (S : Finset (Fin u → ZMod 2)) (hS : S.card = m)
    (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ 2 ^ ell) (sign : Extreme) :
    variationalLower ((m : ℝ) / (2 : ℝ) ^ ell) (2 ^ ell) r ≤
      LinMaxLoad.avgLin (ZMod 2) (Fin u → ZMod 2) ell
        (fun h => extremeAverage S h r sign) ∧
    LinMaxLoad.avgLin (ZMod 2) (Fin u → ZMod 2) ell
        (fun h => extremeAverage S h r sign) ≤
      variationalUpper ((m : ℝ) / (2 : ℝ) ^ ell) (2 ^ ell) r := by sorry

end LinearHashingPoissonesque.ExpectedLoads
