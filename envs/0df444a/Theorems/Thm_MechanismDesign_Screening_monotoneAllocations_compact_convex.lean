-- Prove2me | Theorems.Thm_MechanismDesign_Screening_monotoneAllocations_compact_convex
-- name    : MechanismDesign.Screening.monotoneAllocations_compact_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T22:44:34.360403+00:00
-- url     : https://prove2.me/theorems/47445df9-84cc-4510-af5c-3c1ff7a233da
-- title:
--   Lemma 2.6 -- the set $M$ of increasing $[0,1]$-valued functions is compact and convex
-- statement:
--   Let $0\le\underline\theta<\bar\theta$ and let $M$ be the set of (weakly) increasing functions $q:[\underline\theta,\bar\theta]\to[0,1]$, viewed in the space $\mathcal F$ of functions on $[\underline\theta,\bar\theta]$ with the $L^1$ norm $\|g\|=\int_{\underline\theta}^{\bar\theta}|g|\,d\mu$ ($\mu$ Lebesgue measure). Then
--   $$M \text{ is compact and convex in } \mathcal F .$$
--
--   Compactness and convexity of $M$ are what allow the extreme point theorem (Proposition 2.4) to be applied to the seller's revenue.
--
--   **Formalization Note** $\mathcal F$ is $L^1([\underline\theta,\bar\theta])$ (almost-everywhere classes, a genuine normed space) and $M$ is the set of classes with an increasing representative valued in $[0,1]$; compactness is in the $L^1$-norm topology.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.16, Lemma 2.6

import Mathlib
import Definitions.Def_MechanismDesign_Screening_ExtremePoints

namespace MechanismDesign.Screening

/-- **Lemma 2.6**, p.16. The set `M` of increasing functions `[θ̲, θ̄] → [0, 1]`, as a subset of
`F = L¹([θ̲, θ̄])` with the `L¹` norm, is compact and convex. -/
theorem monotoneAllocations_compact_convex {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi) :
    IsCompact (monotoneAllocations θlo θhi) ∧ Convex ℝ (monotoneAllocations θlo θhi) := by sorry

end MechanismDesign.Screening
