-- Prove2me | Theorems.Thm_HellingerSubadd_hellinger_triangle
-- name    : HellingerSubadd.hellinger_triangle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:49:05.403252+00:00
-- url     : https://prove2.me/theorems/e04d2823-f852-4231-bea1-801aed2fc0d2
-- title:
--   Triangle inequality for the Hellinger distance
-- statement:
--   Let $\mu,\nu,\rho$ be finite measures on a measurable space. Then
--
--   $$
--   D_{\mathrm H}(\mu,\nu)\le D_{\mathrm H}(\mu,\rho)+D_{\mathrm H}(\rho,\nu).
--   $$
--
--   With $\mu=\mathbb P$, $\rho=\mathbb P_\lambda$ and $\nu=\mathbb Q$ this is the display $D_{\mathrm H}(\mathbb P,\mathbb Q)\le D_{\mathrm H}(\mathbb P_\lambda,\mathbb Q)+D_{\mathrm H}(\mathbb P,\mathbb P_\lambda)$ that opens the proof of Lemma A.13 and splits it into Terms I and II.
--
--   Differences from the source:
--   - generalization: probability measures → finite measures; reason: probability measures are finite; the triangle inequality holds for the L²-distance of square-root densities of any finite measures
--   - encoding: D_H as a non-negative real → Real.sqrt (hellingerSq μ ν).toReal; reason: D²_H is finite for finite measures, so toReal loses nothing
-- source:
--   Foster, Kakade, Qian & Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, proof of Lemma A.13, p. 73 (unnumbered display after "Since Hellinger distance satisfies the triangle inequality")

import Mathlib
import Definitions.Def_HellingerSubadd_hellinger

open MeasureTheory
open scoped ENNReal

namespace HellingerSubadd

/-- **Triangle inequality for the Hellinger distance.**
Foster, Kakade, Qian & Rakhlin, *The Statistical Complexity of Interactive Decision Making*,
arXiv:2112.13487v3, proof of Lemma A.13, p. 73 (unnumbered): "Since Hellinger distance satisfies
the triangle inequality, we have D_H(P, Q) ≤ D_H(P_λ, Q) + D_H(P, P_λ)."

For finite measures `μ, ν, ρ` on one measurable space, `D_H(μ, ν) ≤ D_H(μ, ρ) + D_H(ρ, ν)`.
With `μ = P`, `ρ = P_λ`, `ν = Q` this is the paper's display, term for term.

**Formalization Note.** Stated for finite measures, which include the probability measures of
the paper (a generalization). `D_H` is the real square root of `D²_H` (definition `hellinger`). -/
theorem hellinger_triangle {α : Type*} [MeasurableSpace α] (μ ν ρ : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ] :
    hellinger μ ν ≤ hellinger μ ρ + hellinger ρ ν := by sorry

end HellingerSubadd
