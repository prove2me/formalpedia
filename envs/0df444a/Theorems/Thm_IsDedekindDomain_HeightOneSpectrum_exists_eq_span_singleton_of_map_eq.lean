-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_eq_span_singleton_of_map_eq
-- name    : IsDedekindDomain.HeightOneSpectrum.exists_eq_span_singleton_of_map_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/631971c2-561a-5f1e-82c1-655bbd4b5ea3
-- title:
--   Principality of a height-one prime from a pulled-back simple zero
-- statement:
--   Let $R$ be a Dedekind domain with fraction field $K$, let $\mu \colon K \to K$ be a ring homomorphism, and let $N$ be a map from the height-one spectrum of $R$ to $\mathrm{Option}$ of that spectrum, i.e. a partial self-map $v \mapsto N(v)$ of the set of height-one primes. Assume: (i) $N$ hits every prime, that is, for every $w$ there is a $v$ with $N(v) = w$; (ii) $\mu$ transports valuations along $N$, in the sense that whenever $N(v) = w$, every $h \in K$ and every natural number $k$ satisfy the implication $w(h) \le \exp(-k) \Rightarrow v(\mu h) \le \exp(-k)$, where $w(\cdot)$, $v(\cdot)$ are the $\mathbb{Z}^{m0}$-valued valuations of $K$ attached to the primes and $\exp$ is the embedding of $\mathbb{Z}$ into $\mathbb{Z}^{m0}$. Let $g \in K$ and let $t_0$ be a height-one prime of $R$ such that $v(g) = \exp(-1)$ for every $v$ with $N(v) = t_0$, and $v(g) = 1$ for every $v$ with $N(v) = w$ for some $w \neq t_0$; assume further that $g$ lies in the image of $\mu$. Then $t_0$ is principal: there exists $r \in R$ with $t_0 = (r)$. (Only principality is asserted, not that a generator can be taken to be a preimage of $g$.)
--
--   This is the valuation-theoretic core of the non-degeneracy argument for the Weil pairing, in which a function whose divisor would be $(T) - (O)$ is excluded because that divisor is not principal; it is stated here abstractly for an arbitrary Dedekind domain, a partial self-map of its height-one spectrum, and a ring endomorphism of the fraction field compatible with valuations along that map. It is used by [`WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq`](thm.html#WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_eq_span_singleton_of_map_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsDedekindDomain.HeightOneSpectrum.exists_eq_span_singleton_of_map_eq {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (μ : K →+* K) (N : IsDedekindDomain.HeightOneSpectrum R → Option (IsDedekindDomain.HeightOneSpectrum R)) (hN : ∀ w, ∃ v, N v = some w) (hμ : ∀ v w, N v = some w → ∀ (h : K) (k : ℕ), w.valuation K h ≤ WithZero.exp (-(k : ℤ)) → v.valuation K (μ h) ≤ WithZero.exp (-(k : ℤ))) (g : K) (t₀ : IsDedekindDomain.HeightOneSpectrum R) (hg₀ : ∀ v, N v = some t₀ → v.valuation K g = WithZero.exp (-1)) (hg₁ : ∀ v w, N v = some w → w ≠ t₀ → v.valuation K g = 1) (hgμ : ∃ h, μ h = g) : ∃ r : R, t₀.asIdeal = Ideal.span {r} := by sorry
