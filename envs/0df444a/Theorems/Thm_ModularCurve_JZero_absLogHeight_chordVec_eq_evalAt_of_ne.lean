-- Prove2me | Theorems.Thm_ModularCurve_JZero_absLogHeight_chordVec_eq_evalAt_of_ne
-- name    : ModularCurve.JZero.absLogHeight_chordVec_eq_evalAt_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/236d58bc-65f1-5d8a-a996-e617e1d7dd3e
-- title:
--   Chord height at a non-cuspidal place equals the value-tuple height
-- statement:
--   Fix a positive integer $N$ and a natural number $r$, and let $s : \mathrm{Fin}\,r \to \overline{F}_N$ be a family in $\overline{F}_N =$ `modularFunctionFieldBar N`, the subfield of $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the full modular function field of level $N$. Assume `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb{Q}}$ and its $\overline{\mathbb{Q}}$-span is the Riemann–Roch space $\{f : v(f) \le \exp(D(v))$ for all places $v\}$ of the divisor $D = (\mathrm{embDegree}\,N)\cdot \overline{\infty}$ supported at the cusp `cuspInftyBar N`. Let $v, w$ be places of $\overline{F}_N$ over $\overline{\mathbb{Q}}$ (in the project's sense: valuation subrings containing $\overline{\mathbb{Q}}$, proper, with principal ideals), and assume $w \ne$ `cuspInftyBar N`. Write $e_i(v) =$ `evalVec s v i`, the regularised value $v.\mathrm{evalAt}(s_i\, s_{i_0}^{-1})$ at $v$ of $s_i$ divided by the pivot basis element $s_{i_0}$ of minimal order at $v$ (and $0$ when $r = 0$), where $\mathrm{evalAt}$ sends an element of the valuation ring to the preimage in $\overline{\mathbb{Q}}$ of its residue and everything else to $0$. Then the absolute logarithmic height of the chord vector $\big(e_{i}(v)e_{j}(w) - e_{j}(v)e_{i}(w)\big)_{(i,j)}$ equals the absolute logarithmic height of the tuple $\big(w.\mathrm{evalAt}(e_i(v)\cdot s_j - e_j(v)\cdot s_i)\big)_{(i,j)}$, both heights being the $\log$-height of the tuple inside the field it generates over $\mathbb{Q}$, divided by the degree of that field.
--
--   The identity says that away from the cusp at infinity the pivot normalisation built into the chord vector is invisible: the chord coordinates at $w$ are the honest regularised values at $w$ of the chord functions $e_i(v)s_j - e_j(v)s_i$, and the two normalised Weil heights agree. It is used in the estimates for the height pairing on $J_0(N)$, namely in [`ModularCurve.JZero.pairing_chord_self_le_of_prime_of_five_le`](thm.html#ModularCurve.JZero.pairing_chord_self_le_of_prime_of_five_le) and [`ModularCurve.JZero.pairing_principal_le_of_prime_of_five_le`](thm.html#ModularCurve.JZero.pairing_principal_le_of_prime_of_five_le); the proof invokes the rationality of every place of $\overline{F}_N$ (degree one) and the invariance of the normalised logarithmic height under enlarging the field of definition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_absLogHeight_chordVec_eq_evalAt_of_ne.lean

import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.absLogHeight_chordVec_eq_evalAt_of_ne (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (v w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hw : w ≠ cuspInftyBar N) :
    absLogHeight (chordVec s v w)
      = absLogHeight (fun p : Fin r × Fin r => w.evalAt (evalVec s v p.1 • s p.2 - evalVec s v p.2 • s p.1)) := by sorry
