-- Prove2me | Theorems.Thm_HollandsSanders_CFTBound_lemma_13
-- name    : HollandsSanders.CFTBound.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:23.603664+00:00
-- url     : https://prove2.me/theorems/1df718b2-ce89-4518-991d-76e6368319df
-- title:
--   Lemma 13, p. 80 — Δ^{it}_{B′} e^{isD} Δ^{−it}_{B′} = exp[−(is/2) sinh(2πt)(P⁰+K⁰) + is cosh(2πt) D]
-- statement:
--   Consider a conformal field theory in $d+1$ dimensions, $d\ge2$, in its vacuum representation, and let $\Delta_{B'}$ be the modular operator of the algebra $\mathfrak A_{B'}$ of the double cone over the unit ball, with the vacuum vector. For all $s,t\in\mathbb R$,
--   $$\Delta_{B'}^{it}\,e^{isD}\,\Delta_{B'}^{-it}=\exp\Big[-\frac{is}{2}\sinh(2\pi t)\,(P^0+K^0)+is\cosh(2\pi t)\,D\Big]$$
--   on $\mathcal H_0$, where $D$ is the dilation generator and $\tfrac12(P^0+K^0)$ the conformal Hamiltonian.
--
--   The identity expresses the modular flow of the double cone, conjugating dilations, in terms of the conformal generators; continued analytically to $t=-i/4$ it yields the operator identity (212).
--
--   **Formalization Note.** The right side is the one-parameter unitary $e^{isG(X)}$ of the Lie algebra element $X=-\sinh(2\pi t)M_{0(d+2)}+\cosh(2\pi t)M_{(d+1)(d+2)}$, with $G(M_{0(d+2)})=\tfrac12(P^0+K^0)$ and $G(M_{(d+1)(d+2)})=D$ as in the definition file. The lemma is stated for the unit ball, the normalization $R=1$ of the proof of Theorem 13.
-- source:
--   Hollands & Sanders, Entanglement measures and their properties in quantum field theory, arXiv:1702.04924v3, p. 80, Lemma 13 (216), with (217)–(218)

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HollandsSanders_CFTBound_Entanglement
import Definitions.Def_HollandsSanders_CFTBound_Conformal
open OAI.BoundedRecovery Real
open scoped InnerProductSpace ENNReal

namespace HollandsSanders.CFTBound

/-- Lemma 13 (p. 80), for `B′` the unit double cone (`R = 1`, as in the proof):
`Δ_{B′}^{it} e^{isD} Δ_{B′}^{−it} = exp[−(is/2) sinh(2πt)(P⁰ + K⁰) + is cosh(2πt) D]`. The right
side is `exp(i s G(X))` for `X = −sinh(2πt) M_{0(d+2)} + cosh(2πt) M_{(d+1)(d+2)}`, since
`G(M_{0(d+2)}) = ½(P⁰ + K⁰)` and `G(M_{(d+1)(d+2)}) = D`. -/
theorem lemma_13 {d : ℕ} (hd : 2 ≤ d) {H0 : Type*} [NormedAddCommGroup H0]
    [InnerProductSpace ℂ H0] [CompleteSpace H0] (T : CFTVacuum d H0)
    (S : StandardModularData H0) (hS : S.M = T.net (ballDiamond 1)) (hx : S.xi = T.vac)
    (s t : ℝ) :
    S.D.unitary t * T.Dil.unitary s * S.D.unitary (-t) =
      T.expiGen (-(Real.sinh (2 * π * t)) • genM d 0 (idxQ d) +
        Real.cosh (2 * π * t) • genM d (idxP d) (idxQ d)) s := by sorry

end HollandsSanders.CFTBound
