-- Prove2me | Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_potential_poisson
-- name    : LinearHashingPoissonesque.ExpectedLoads.potential_poisson
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T19:03:05.90721+00:00
-- url     : https://prove2.me/theorems/6bfb96fb-9e03-425e-ae9b-2f0c5e4373ce
-- title:
--   Theorem 7 — the potential–Poisson inequality for every real parameter
-- statement:
--   Let $u\ge\ell\ge1$ and $m\ge1$ be integers. Put $n=2^\ell$ and $\mu=m/n$. Fix an arbitrary set $S\subseteq\mathbb F_2^u$ of size $m$ and any $\lambda\in\mathbb R$. For $h$ uniformly distributed among all linear maps $\mathbb F_2^u\to\mathbb F_2^\ell$,
--
--   $$\mathbb E_h[\phi_\lambda(S,h)]\le\mu(e^\lambda-\lambda-1).$$
--
--   This compares the expected centered logarithmic potential to the centered Poisson cumulant expression. The zero vector may belong to $S$; no independence of its elements or rank condition on $h$ is assumed. Every real parameter, including negative parameters and zero, is included.
--
--   Differences from the source:
--   - encoding: binary coordinate spaces, n = 2^ℓ and μ = m/n → Fin u → ZMod 2 and Fin ℓ → ZMod 2, with n and μ substituted in the formulas; reason: these coordinate spaces have exactly the source cardinalities, and ℓ is independent of m
--   - encoding: expectation under the uniform law on all linear maps → LinMaxLoad.avgLin, a finite sum divided by the number of all linear maps; reason: the published definition includes singular maps and introduces no conditioning or regularity assumptions
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.10, Theorem 7; introduction Eq.(1), p.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf

import Definitions.Def_LinMaxLoad_avgLin
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_LogPotential
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_ExtremeLoads

namespace LinearHashingPoissonesque.ExpectedLoads

/-- Theorem 7, p.10: all linear maps, arbitrary real λ, and all subsets S of size m. -/
theorem potential_poisson {u ell m : ℕ} (hu : ell ≤ u) (hell : 1 ≤ ell) (hm : 1 ≤ m)
    (S : Finset (Fin u → ZMod 2)) (hS : S.card = m) (lam : ℝ) :
    LinMaxLoad.avgLin (ZMod 2) (Fin u → ZMod 2) ell
      (fun h => logPotential S h lam) ≤
    ((m : ℝ) / (2 : ℝ) ^ ell) * (Real.exp lam - lam - 1) := by sorry

end LinearHashingPoissonesque.ExpectedLoads
