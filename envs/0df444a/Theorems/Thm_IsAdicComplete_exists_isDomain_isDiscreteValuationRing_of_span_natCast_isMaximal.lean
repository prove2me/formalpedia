-- Prove2me | Theorems.Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_natCast_isMaximal
-- name    : IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_span_natCast_isMaximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/2a75410d-be2f-5edf-a09f-6e885cabaafe
-- title:
--   Complete rings with (p) maximal and p regular are DVRs
-- statement:
--   Let $\mathcal{O}$ be a commutative ring and $p$ a natural number (no primality is assumed). Suppose that the image of $p$ in $\mathcal{O}$ is a non-zero-divisor, i.e. lies in the submonoid `nonZeroDivisors 𝓞`, that the principal ideal $\mathrm{span}\{p\cdot 1\}$ is maximal, and that $\mathcal{O}$ is adically complete for this ideal, in the sense of Mathlib's `IsAdicComplete` (the $(p)$-adic topology is Hausdorff, so $\bigcap_n (p^n) = 0$, and every $(p)$-adically Cauchy sequence has a limit). Then there exist instances witnessing that $\mathcal{O}$ is an integral domain and that $\mathcal{O}$ is a discrete valuation ring, and moreover $p\cdot 1$ is irreducible in $\mathcal{O}$ and the maximal ideal of $\mathcal{O}$ as a local ring equals $\mathrm{span}\{p\cdot 1\}$. The conclusion is phrased as an existential statement over the two class instances, so that the final two assertions are stated relative to the domain and discrete-valuation-ring structures just produced; the residue field $\mathcal{O}/(p)$ is arbitrary.
--
--   This is the standard recognition criterion for a complete discrete valuation ring with uniformiser $p$: a $(p)$-adically complete ring in which $p$ is regular and generates a maximal ideal. It is used in the treatment of multivariate formal groups over such a coefficient ring $\mathcal{O}$, where it supplies the domain, discrete-valuation and uniformiser structure on $\mathcal{O}$ needed for the torsion-ideal and finite-freeness statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_natCast_isMaximal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_span_natCast_isMaximal
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {(p : 𝓞)}).IsMaximal] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] :
    ∃ (_ : IsDomain 𝓞) (_ : IsDiscreteValuationRing 𝓞),
      Irreducible (p : 𝓞) ∧ IsLocalRing.maximalIdeal 𝓞 = Ideal.span {(p : 𝓞)} := by sorry
