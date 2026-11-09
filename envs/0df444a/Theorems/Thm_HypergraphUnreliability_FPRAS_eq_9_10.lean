-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_eq_9_10
-- name    : HypergraphUnreliability.FPRAS.eq_9_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:09.326326+00:00
-- url     : https://prove2.me/theorems/f8f6d440-3545-43ce-847b-a876b40a6342
-- title:
--   Equations (9.8)–(9.10) — finite sampling of the weighted process
-- statement:
--   On the connected quotient, take the weighted parameters: $M_0=\max\{1,R\}$, $L^\prime=\lceil1024NM_0^2/\varepsilon\rceil$, $h^\prime=1/L^\prime$, and $q^\prime$ from (9.9). Let $\hat F$ be the implemented reward of one sample, $\nu^\prime=E\hat F$, and $\mu^\prime=e^\Lambda u^\prime$. Then $h^\prime R\le1$, the Euler error and the fixed-bit error satisfy
--   $$\frac{R^2}{L^\prime}\le\frac{\varepsilon}{1024N},\qquad [N+L^\prime(2m+2)]2^{-q^\prime}\le\frac{\varepsilon}{1024N},$$
--   and
--   $$|\nu^\prime-\mu^\prime|\le\frac{\varepsilon}{512},\qquad 0\le\hat F\le N,\qquad \mathrm{Var}(\hat F)\le N\nu^\prime\le2N\mu^\prime.$$
--
--   The horizon is exactly $1$, so there is no horizon error. The bias is additive in a quantity with mean at least one.
--
--   Differences from the source: none.
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), §9.4, (9.8)–(9.10), p. 14

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_WeightedAlgorithm

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

open LabeledHypergraph

/-- (9.8)–(9.10), p. 14: finite sampling. For the weighted parameters on the connected quotient, with
`F̂` the reward of one implemented sample and `ν′ = E F̂`: the Euler probabilities are valid
(`h′ R ≤ 1`), the Euler error `R²/L′` and the fixed-bit error `[N + L′(2m+2)] 2^{-q′}` are each at most
`ε/(1024 N)`, and `|ν′ - μ′| ≤ ε/512`, `0 ≤ F̂ ≤ N`, `Var F̂ ≤ N ν′ ≤ 2 N μ′`, where `μ′ = e^Λ u′`. -/
theorem eq_9_10 (D : QuotientData) (hD : D.Regular) (ε δ : ℚ) (h0 : 0 < ε) (h1 : ε < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    let P := D.params ε δ
    let bits := P.sampleBits
    let F : (Fin bits → Bool) → ℝ := fun ω => ((P.sampleReward (tapeBit ω) 0 : ℚ) : ℝ)
    let ν := fairExpect bits F
    let μ := D.normalizedMean ε
    (1 / (D.L' ε : ℚ)) * D.R ε ≤ 1 ∧
    (D.R ε) ^ 2 / (D.L' ε : ℚ) ≤ ε / (1024 * D.N) ∧
    (D.N + (D.L' ε : ℚ) * (2 * D.m + 2)) * (1 / 2 : ℚ) ^ P.q ≤ ε / (1024 * D.N) ∧
    |ν - μ| ≤ (ε : ℝ) / 512 ∧
    (∀ ω, 0 ≤ F ω ∧ F ω ≤ ((D.N : ℚ) : ℝ)) ∧
    fairExpect bits (fun ω => F ω ^ 2) - ν ^ 2 ≤ ((D.N : ℚ) : ℝ) * ν ∧
    ((D.N : ℚ) : ℝ) * ν ≤ 2 * ((D.N : ℚ) : ℝ) * μ := by sorry

end HypergraphUnreliability.FPRAS
