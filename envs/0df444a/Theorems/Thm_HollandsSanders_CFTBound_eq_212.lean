-- Prove2me | Theorems.Thm_HollandsSanders_CFTBound_eq_212
-- name    : HollandsSanders.CFTBound.eq_212
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:15.16016+00:00
-- url     : https://prove2.me/theorems/6d4301d0-64b2-400d-9200-e2922f99eaad
-- title:
--   Eqs. (211)–(212), pp. 79–81 — T = Δ^{1/4}_{B′} Δ^{−1/4}_A = r^{½(P⁰+K⁰)} r^{iD}
-- statement:
--   In a conformal field theory in $d+1$ dimensions, $d\ge2$, let $0<r<1$, and let $\Delta_A$ and $\Delta_{B'}$ be the modular operators of the algebras of the double cones over the balls of radius $r$ and $1$, with the vacuum vector. The operator
--   $$T=\Delta_{B'}^{1/4}\,\Delta_A^{-1/4}\qquad(211)$$
--   satisfies
--   $$T=r^{\frac12(P^0+K^0)}\,r^{iD}.\qquad(212)$$
--   Precisely: every $x$ in the domain of $\Delta_A^{1/4}$ lies in the domain of $\Delta_{B'}^{1/4}$, and
--   $$\Delta_{B'}^{1/4}x=r^{\frac12(P^0+K^0)}\,r^{iD}\,\Delta_A^{1/4}x.$$
--
--   Since $r^{iD}$ is unitary, $T$ has the same 1-nuclear norm as $r^{\frac12(P^0+K^0)}$, namely $\operatorname{Tr}r^{\frac12(P^0+K^0)}$; this is the source of the bound of Theorem 13.
--
--   **Formalization Note.** $r^{\frac12(P^0+K^0)}$ is $e^{(\ln r)\cdot\frac12(P^0+K^0)}$, defined by the bounded function $u\mapsto r^{\max(u,0)}$ of the conformal Hamiltonian, whose spectrum is non-negative (footnote 42); $r^{iD}=e^{i(\ln r)D}$. The identity is stated on the range of $\Delta_A^{1/4}$, which is dense, avoiding the unbounded inverse.
-- source:
--   Hollands & Sanders, Entanglement measures and their properties in quantum field theory, arXiv:1702.04924v3, pp. 79–81, eqs. (211)–(212), proved on p. 81

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HollandsSanders_CFTBound_Entanglement
import Definitions.Def_HollandsSanders_CFTBound_Conformal
open OAI.BoundedRecovery Real
open scoped InnerProductSpace ENNReal

namespace HollandsSanders.CFTBound

/-- (211)–(212), pp. 79–81: for `0 < r < 1`, `T = Δ_{B′}^{1/4} Δ_A^{−1/4} = r^{½(P⁰+K⁰)} r^{iD}`,
stated on the range of `Δ_A^{1/4}`: every `x` in the domain of `Δ_A^{1/4}` lies in the domain of
`Δ_{B′}^{1/4}` and `Δ_{B′}^{1/4} x = r^{L0} r^{iD} Δ_A^{1/4} x`. Here `r^{L0} = e^{(ln r) L0}` and
`r^{iD} = e^{i(ln r)D}`. -/
theorem eq_212 {d : ℕ} (hd : 2 ≤ d) {H0 : Type*} [NormedAddCommGroup H0]
    [InnerProductSpace ℂ H0] [CompleteSpace H0] (T : CFTVacuum d H0)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (SA SB : StandardModularData H0)
    (hSA : SA.M = T.net (ballDiamond r)) (hxA : SA.xi = T.vac)
    (hSB : SB.M = T.net (ballDiamond 1)) (hxB : SB.xi = T.vac) (x y : H0)
    (hxy : (x, y) ∈ quarterGraph SA) :
    (x, T.L0.calculus (expDecay (-Real.log r)) (T.Dil.unitary (Real.log r) y)) ∈ quarterGraph SB := by sorry

end HollandsSanders.CFTBound
