-- Prove2me | Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_remove_surjectivity
-- name    : LinearHashingPoissonesque.ExpectedLoads.remove_surjectivity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T19:02:55.507007+00:00
-- url     : https://prove2.me/theorems/588ecc05-df2c-484c-8038-c63f33a1dab2
-- title:
--   Lemma 1 — lossless removal of surjectivity over finite fields
-- statement:
--   Let $K$ be any finite field with $q=|K|$, and let $\ell,m\ge1$ and $1\le r\le q^\ell$ be integers. Let $f:\Sigma^{K^\ell}(m)\to[0,\infty)$ be arbitrary and $a\ge0$ be a finite real number. Suppose that for infinitely many integers $U\ge\ell$, every set $S\subseteq K^U$ of size $m$ satisfies
--
--   $$\mathbb E_{h\text{ uniform surjective linear }K^U\to K^\ell}[f(\vec L(S,h))]\le a.$$
--
--   Then, for every $u\ge\ell$ and every $S\subseteq K^u$ of size $m$,
--
--   $$\mathbb E_{h\text{ uniform linear }K^u\to K^\ell}[f(\vec L(S,h))]\le a.$$
--
--   The same statistic and the same bound apply across all dimensions. The statistic may depend on bin labels and need not be monotone or symmetric. All finite fields are covered, including fields of nonprime prime-power cardinality. The printed parameter $r$ is retained even though it does not enter the displayed inequality.
--
--   Differences from the source:
--   - encoding: a prime power q and the field F_q → an arbitrary finite field K with q = Fintype.card K and coordinate spaces Fin d → K; reason: every finite field has prime-power cardinality, including nonprime prime powers; no ZMod q restriction is imposed
--   - encoding: a nonnegative real statistic on labelled vectors of total mass m → LoadVector (Fin ℓ → K) m → NNReal, evaluated at labelledLoads S hS h; reason: the subtype enforces only the sum of the loads; NNReal represents exactly the finite nonnegative reals
--   - encoding: infinitely many U ≥ ℓ with a surjective-map expectation bound for every size-m S → Set.Infinite of those dimensions and LinMaxLoad.condAvgLin with Function.Surjective; reason: the conditional average is the uniform surjection law; U ≥ ℓ admits surjections, as proved locally
--   - encoding: expectation under the uniform law on all linear maps → LinMaxLoad.avgLin, a finite sum divided by the number of all linear maps; reason: the published definition includes singular maps and introduces no conditioning or regularity assumptions
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.9, Lemma 1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf

import Definitions.Def_LinMaxLoad_condAvgLin
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_LoadVector

namespace LinearHashingPoissonesque.ExpectedLoads

/-- Lemma 1, p.9: the same labelled statistic and bound for infinitely many dimensions.
A finite field K includes every prime power; r is retained although unused in the inequality. -/
theorem remove_surjectivity (K : Type*) [Field K] [Fintype K]
    (ell m r : ℕ) (hell : 1 ≤ ell) (hm : 1 ≤ m)
    (hr : 1 ≤ r) (hrq : r ≤ Fintype.card K ^ ell)
    (f : LoadVector (Fin ell → K) m → NNReal) (a : ℝ) (ha : 0 ≤ a)
    (hgood : Set.Infinite {U : ℕ | ell ≤ U ∧
      ∀ (S : Finset (Fin U → K)) (hS : S.card = m),
        LinMaxLoad.condAvgLin K (Fin U → K) ell
          (fun h => Function.Surjective h)
          (fun h => (f (labelledLoads S hS h) : ℝ)) ≤ a})
    (u : ℕ) (hu : ell ≤ u) (S : Finset (Fin u → K)) (hS : S.card = m) :
    LinMaxLoad.avgLin K (Fin u → K) ell
      (fun h => (f (labelledLoads S hS h) : ℝ)) ≤ a := by sorry

end LinearHashingPoissonesque.ExpectedLoads
