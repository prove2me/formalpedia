-- Prove2me | Theorems.Thm_KramersHubbard_PartitionFunction_worm_gap
-- name    : KramersHubbard.PartitionFunction.worm_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:53.660138+00:00
-- url     : https://prove2.me/theorems/af96b965-1b68-4b6d-85f6-8e239e4f98b6
-- title:
--   Proposition 8 — Spectral gap of the lazy worm chain
-- statement:
--   Let $G$ be the concrete Green matrix of an attractive Kramers input with $\beta>0$, $M\ge1$, $r\ge1$, and $K=[M]\times[2r]$. For every $0<\lambda<1$, the actual lazy worm chain of Section 4.3 is stochastic, reversible and stationary for $\pi_\lambda$, and
--
--   $$\operatorname{gap}(P_\lambda)\ge\frac{\lambda}{2|K|}.$$
--
--   Equivalently, its Dirichlet form is at least $\lambda/(2|K|)$ times the variance of every real function on positive support. Every heat-bath denominator from such a state is positive; every supported stationary weight is positive and the weights sum to one. The factor $1/2$ from laziness is retained. This item proves these properties of the computed kernel rather than assuming a fast sampler.
--
--   Differences from the source:
--   - encoding: the chain is described on equal-size configurations with nonnegative weights → the kernel is restricted to exactly nonzero-weight configurations and the gap bound is stated in its real Poincare form; reason: on attractive inputs nonzero weights are positive; all positive configurations remain, singleton variance is zero with the conventional gap one, and the source update is undefined only when |K|=0
--   - encoding: stochasticity and detailed balance are stated in Section 4.3, with the gap in Proposition 8 → normalization, positive denominators, stochasticity, detailed balance, stationarity and the gap are one conjunction; reason: all are properties of the same explicit source kernel, without hidden hypotheses
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Ojas Parekh, Andrew Zhao, STOC 2027 submission #1325 (October 2026), Efficient classical simulation of Fermi-Hubbard models with Kramers symmetry, Proposition 8, p.20, proof p.21; Section 4.3, p.16; printed page = 1-based PDF page. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1325.pdf; PDF SHA-256 e3fd3fa7390d8ff9f0f1e2ee07e6ebc5b8d7304e26be9e76959d9587f4564eae. Canonical submitted artifact, citation_basis: published; title-page date November 3, 2026; no assertion of conference acceptance.

import Definitions.Def_KramersHubbard_PartitionFunction_Worm

noncomputable section
open scoped BigOperators
open Matrix MeasureTheory

namespace KramersHubbard.PartitionFunction

/-- Proposition 8, pp.20-21, including well-definedness and detailed balance
    stated in Section 4.3. No positivity, stationarity or gap is an input promise. -/
theorem worm_gap {N r M : ℕ} (D : Data N r) (hD : Attractive D)
    (β : ℝ) (hβ : 0 < β) (hM : 0 < M) (hr : 0 < r)
    (lam : ℝ) (hlam : 0 < lam ∧ lam < 1) :
    let G := green (M := M) D β
    let pi := fun s : WormSupport G lam => wormLaw G lam s.val
    let P := wormKernel G lam
    wormWeight G lam (emptyConfiguration (M * (2*r))) = 1 ∧
    (∀ s : WormSupport G lam, ∀ c, downAllowed s.val c →
      ∃ a : ℝ, 0 < a ∧ restoreDenominator G (downState s.val c) = (a : ℂ)) ∧
    (∀ s : WormSupport G lam, ∃ a : ℝ, 0 < a ∧ pi s = (a : ℂ)) ∧
    (∑ s : WormSupport G lam, pi s) = 1 ∧
    Stochastic P ∧ DetailedBalance pi P ∧ Stationary pi P ∧
    GapAtLeast pi P (lam / (2 * (M * (2*r) : ℕ))) := by sorry

end KramersHubbard.PartitionFunction
