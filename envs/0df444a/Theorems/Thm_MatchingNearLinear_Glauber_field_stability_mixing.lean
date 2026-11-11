-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_field_stability_mixing
-- name    : MatchingNearLinear.Glauber.field_stability_mixing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:55:44.592192+00:00
-- url     : https://prove2.me/theorems/5bf1c012-a4e3-4c3b-8b07-ad2d23a852c3
-- title:
--   Theorem 1.4 — Glauber mixing from field-dynamics spectral stability
-- statement:
--   There is a universal constant $c>0$. Let $N\ge1$ and let $p$ be a probability law positive on a downward-closed support with at least two states. Suppose $\kappa\ge1$, $0<b\le1$, and $C:[0,1)\to[1,\infty)$ is nonincreasing. Assume spectral stability after every positive pin of every scalar-field law, finite $I=\int_0^1(C(t)-1)/(1-t)\,dt$, insertion ratios at most $\kappa$, and occupied marginals under every feasible positive pin at least $b$. Write $p_{\min}=\min_{S\in\Omega}p(S)$. Then
--
--   $$\operatorname{Ent}_p(f^2)\le c\kappa e^I N\log(N\kappa/b)\mathcal E_{\rm GD}(f,f),$$
--
--   for all real $f$, and for $0<\varepsilon\le1/2$,
--
--   $$t_{\rm mix}(\varepsilon)\le c\kappa e^I N\left[\log(N\kappa/b)\log\log(e^2/p_{\min})+\log(1/\varepsilon)\right].$$
--
--   For any fixed bounds $\kappa\le\kappa_0$, $I\le I_0$ and $b\ge N^{-d}$ with $N\ge2$, $\kappa_0\ge1$ and $I_0,d\ge0$, there is a constant depending only on those fixed bounds giving inverse LSI $O(N\log N)$ and mixing $O(N[\log^2N+\log(1/\varepsilon)])$. These are both conclusions, not extra hypotheses on the kernel. This is the analytic criterion applied to matchings.
--
--   Differences from the source:
--   - encoding: a probability law positive on its actual subset support → a nonnegative normalized mass function on all subsets, with functions on its strictly positive support subtype; reason: zero-weight configurations add no instances or hypotheses
--   - encoding: an upper bound on the inverse optimal log-Sobolev or modified log-Sobolev constant → the corresponding functional inequality with the asserted coefficient; reason: these are equivalent for the source irreducible finite kernels and avoid default values for invalid extrema
--   - encoding: least nonnegative integer worst-start mixing time bounded by B → existence of a natural horizon t with t ≤ B and total-variation error at most epsilon from every starting state; reason: this is equivalent to the least-time bound and certifies a nonempty set of mixing times
--   - encoding: parameter-uniform or universal big-O bounds → a positive existential constant before all instance parameters; secondary asymptotic clauses quantify fixed bounds first; reason: this is the precise uniform meaning of the source asymptotic notation
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Theorem 1.4, printed p. 4 (PDF p. 6); continues on printed p.5 (PDF p.7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_SubsetLaws

set_option autoImplicit false

namespace MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/

theorem field_stability_mixing :
    (∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ∀ p : Config N → ℝ,
      IsSubsetLaw p → DownwardClosed p → 2 ≤ Fintype.card (Support p) →
      ∀ κ b : ℝ, 1 ≤ κ → 0 < b → b ≤ 1 → ∀ C : ℝ → ℝ,
      RateConditions C → SpectralStability p C → RatioBound p κ → OccupiedLowerBound p b →
      LSIBound (supportMass p) (subsetGlauber p)
        (c*κ*Real.exp ((stabilityIntegral C).toReal)*N*Real.log ((N:ℝ)*κ/b)) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
      MixingBound (supportMass p) (subsetGlauber p) ε
        (c*κ*Real.exp ((stabilityIntegral C).toReal)*N *
          (Real.log ((N:ℝ)*κ/b)*Real.log (Real.log (Real.exp 2/minMass (supportMass p))) +
            Real.log (1/ε)))) ∧
    (∀ κ₀ I₀ d : ℝ, 1 ≤ κ₀ → 0 ≤ I₀ → 0 ≤ d → ∃ D : ℝ, 0 < D ∧
      ∀ N : ℕ, 2 ≤ N → ∀ p : Config N → ℝ,
      IsSubsetLaw p → DownwardClosed p → 2 ≤ Fintype.card (Support p) →
      ∀ κ b : ℝ, 1 ≤ κ → κ ≤ κ₀ → 0 < b → b ≤ 1 → (N:ℝ)^(-d) ≤ b →
      ∀ C : ℝ → ℝ, RateConditions C → (stabilityIntegral C).toReal ≤ I₀ →
      SpectralStability p C → RatioBound p κ → OccupiedLowerBound p b →
      LSIBound (supportMass p) (subsetGlauber p) (D*N*Real.log N) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → MixingBound (supportMass p) (subsetGlauber p) ε
        (D*N*((Real.log N)^2+Real.log (1/ε)))) := by sorry

end MatchingNearLinear.Glauber
