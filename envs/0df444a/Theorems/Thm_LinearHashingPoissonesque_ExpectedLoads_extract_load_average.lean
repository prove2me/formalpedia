-- Prove2me | Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_extract_load_average
-- name    : LinearHashingPoissonesque.ExpectedLoads.extract_load_average
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-09T19:02:56.039705+00:00
-- url     : https://prove2.me/theorems/2f7f654c-51bf-415b-99fe-763687d87021
-- title:
--   Lemma 3 — extraction of either extreme-bin average
-- statement:
--   Let $u\ge\ell\ge1$, put $n=2^\ell$, and let $1\le r\le n$. Fix a set $S\subseteq\mathbb F_2^u$, put $\mu=|S|/n$, and let $f:\mathbb F_2^u\to\mathbb F_2^\ell$ be an arbitrary function. For every $\lambda\in\mathbb R$ and each sign $\star\in\{-,+\}$,
--
--   $$\phi_\lambda(S,f)\ge\lambda(L_r^\star(S,f)-\mu)-\log(n/r).$$
--
--   The same statement applies to both the heaviest and the lightest $r$ bins with either sign of $\lambda$. No linearity is required of $f$. This relates the deterministic load statistics to the centered potential before any expectation is taken.
--
--   Differences from the source:
--   - encoding: the fixed set S, real λ, μ = |S|/n and the two signs in the section setup → explicit S and lam binders, the computed center, and the two constructors of Extreme; reason: the source omits S and λ from the lemma sentence but uses them in its formula
--   - encoding: the r smallest or r largest entries of the full n-bin multiset → the first r terms of the increasing list or its reverse, summed and divided by r in ℝ; reason: all zero-load bins and all multiplicities are retained; the value does not depend on tie ordering
--   - generalization: S in the positive-cardinality setup for the expected-load application → any finite S, including the empty set; reason: the deterministic inequality also holds at S = ∅; restricting to the source setup recovers every source instance
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.12, Lemma 3, with Section 3 standing S and λ; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf

import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_LogPotential
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_ExtremeLoads

namespace LinearHashingPoissonesque.ExpectedLoads

/-- Lemma 3, p.12: fixed S and λ from the section preamble, and either sign.
The hash function is arbitrary. μ is computed from the actual set S. -/
theorem extract_load_average {u ell : ℕ} (hu : ell ≤ u) (hell : 1 ≤ ell)
    (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ 2 ^ ell)
    (S : Finset (Fin u → ZMod 2)) (f : (Fin u → ZMod 2) → (Fin ell → ZMod 2))
    (lam : ℝ) (sign : Extreme) :
    lam * (extremeAverage S f r sign - (S.card : ℝ) / (2 : ℝ) ^ ell) -
      Real.log (((2 : ℝ) ^ ell) / (r : ℝ)) ≤ logPotential S f lam := by sorry

end LinearHashingPoissonesque.ExpectedLoads
