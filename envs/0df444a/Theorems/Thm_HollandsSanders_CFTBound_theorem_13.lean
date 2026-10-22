-- Prove2me | Theorems.Thm_HollandsSanders_CFTBound_theorem_13
-- name    : HollandsSanders.CFTBound.theorem_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:31.164581+00:00
-- url     : https://prove2.me/theorems/dfd1c628-7293-4c7d-a01a-a4a5c358df8b
-- title:
--   Theorem 13, p. 79 — CFT vacuum: E_R(ω₀) ⩽ ln Tr (r/R)^{½(P⁰+K⁰)} for a ball of radius r and the outside of a concentric ball of radius R
-- statement:
--   Consider a conformal quantum field theory in $d+1$ dimensions, $d\ge2$, in its vacuum representation on $\mathcal H_0$, with vacuum state $\omega_0(x)=\langle0|x|0\rangle$. Let $R>r>0$, let $A$ be the ball of radius $r$ and $B$ the complement of the ball of radius $R$, both centred at the origin of the time slice $x^0=0$, and let $\mathfrak A_A=\pi_0(\mathfrak A(O_A))''$, $\mathfrak A_B=\pi_0(\mathfrak A(O_B))''$ be the von Neumann algebras of their domains of dependence. Then the relative entanglement entropy of the vacuum between $\mathfrak A_A$ and $\mathfrak A_B$ satisfies
--   $$E_R(\omega_0)\leqslant\ln\operatorname{Tr}\Big(\frac rR\Big)^{\frac12(P^0+K^0)},$$
--   where $\tfrac12(P^0+K^0)$ is the conformal Hamiltonian.
--
--   The bound expresses the vacuum entanglement between a ball and the outside of a larger concentric ball through the partition function of the conformal Hamiltonian at inverse temperature $\ln(R/r)$; it is finite whenever that partition function is.
--
--   **Formalization Note.** $E_R$ is the infimum of Araki's relative entropy (Kosaki's form) over separable normal states on the join $\mathfrak A_A\vee\mathfrak A_B$, $+\infty$ if there is none; no split property is assumed. The trace of the positive operator $(r/R)^{\frac12(P^0+K^0)}$ is taken in $[0,\infty]$ and the logarithm in $(-\infty,\infty]$, so a divergent trace gives the trivial bound $+\infty$. $d\ge2$ is the restriction $d>1$ of §4.4 (p. 78).
-- source:
--   Hollands & Sanders, Entanglement measures and their properties in quantum field theory, arXiv:1702.04924v3, p. 79, Theorem 13 (210)

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HollandsSanders_CFTBound_Entanglement
import Definitions.Def_HollandsSanders_CFTBound_Conformal
open OAI.BoundedRecovery Real
open scoped InnerProductSpace ENNReal

namespace HollandsSanders.CFTBound

/-- Theorem 13 (p. 79): for `R > r > 0`, `A` the double cone of the ball of radius `r` and `B` the
domain of dependence of the complement of the concentric ball of radius `R`, the vacuum state
`ω₀` satisfies `E_R(ω₀) ⩽ ln Tr (r/R)^{½(P⁰+K⁰)}` (210). -/
theorem theorem_13 {d : ℕ} (hd : 2 ≤ d) {H0 : Type*} [NormedAddCommGroup H0]
    [InnerProductSpace ℂ H0] [CompleteSpace H0] (T : CFTVacuum d H0)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ER (T.net (ballDiamond r)) (T.net (outside R)) (vecState T.vac) ≤
      ENNReal.log (traceENN (T.L0.calculus (expDecay (-Real.log (r / R))))) := by sorry

end HollandsSanders.CFTBound
