-- Prove2me | Theorems.Thm_ModularCurve_JZero_pairing_principal_le_of_prime_of_five_le
-- name    : ModularCurve.JZero.pairing_principal_le_of_prime_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/0d7fbb46-b47f-5963-bcb0-3f5c3772473f
-- title:
--   Height pairing against principal divisors is almost zero
-- statement:
--   Fix a natural number $N$, nonzero, prime and at least $5$, and consider the function field $\overline{M}_N =$ `modularFunctionFieldBar N`, the base change to $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` of the full modular function field of level $N$, viewed inside Laurent series. Let $r$ be a natural number and $s : \mathrm{Fin}\,r \to \overline{M}_N$ a family which is an embedding basis in the sense of `IsEmbBasis`: $s$ is linearly independent over $\overline{\mathbb Q}$ and its span equals the Riemann–Roch space $\{f : v.\mathrm{adicValuation}\,f \le \exp(D\,v)\ \text{for all places}\ v\}$ of the divisor `embDivisor N`. Write $h(v) =$ `pointHt s v` for the absolute logarithmic height of the normalised evaluation vector of $s$ at a place $v$, $b(v,w) = h(v) + h(w) -$ `absLogHeight (chordVec s v w)` for the pair height, and $t(w) =$ `baseHt s (cuspInftyBar N) w`, which is $0$ when $w$ is the cusp $\overline{\infty}$ and $b(w,\overline\infty)$ otherwise; let $g$ be `genusFF`, the $\overline{\mathbb Q}$-dimension of $H^1$ of the zero divisor. The assertion: for every $\varepsilon > 0$ there is a real constant $c$ such that for every $f \in \overline{M}_N$, every finitely supported divisor $A$ on the places of $\overline{M}_N$ with $A\,w = \mathrm{ord}_w f$ for all $w$, and every place $v$,
--   $$\Bigl|\sum_{w \neq v} A(w)\bigl(t(w) - b(v,w)\bigr) + (2g-1)\,A(v)\,t(v)\Bigr| \le \varepsilon\,|A(v)|\,h(v) + c\sum_{w} |A(w)|,$$
--   the sums being the Finsupp sums over $A$ with $v$ erased, respectively over $A$. No nonvanishing hypothesis is imposed on $f$; the constant $c$ depends only on $N$, $s$ and $\varepsilon$, not on $f$, $A$ or $v$.
--
--   This is the quasi-orthogonality statement for the pair-height pairing: pairing a place against the divisor of a function contributes nothing beyond an error that is linear in the total mass $\sum_w |A(w)|$ of the divisor and arbitrarily small relative to the self-height $|A(v)|h(v)$, the coefficient $2g-1$ recording the self-pairing convention of the height form. It feeds the quasi-invariance results [`ModularCurve.JZero.heightForm_quasiInvariant_eps_of_prime_of_five_le`](thm.html#ModularCurve.JZero.heightForm_quasiInvariant_eps_of_prime_of_five_le) and [`ModularCurve.JZero.heightForm_quasiInvariant_of_prime_of_five_le`](thm.html#ModularCurve.JZero.heightForm_quasiInvariant_of_prime_of_five_le), which descend the height form to the degree-zero class group `JZero N`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_pairing_principal_le_of_prime_of_five_le.lean

import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.pairing_principal_le_of_prime_of_five_le (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N)
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, ∀ (f : modularFunctionFieldBar N)
      (A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      (∀ w, A w = w.ord f) →
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        |((A.erase v).sum fun w m => (m : ℝ) * (baseHt s (cuspInftyBar N) w - pairHt s v w))
          + (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 1)
            * (A v : ℝ) * baseHt s (cuspInftyBar N) v|
        ≤ ε * |(A v : ℝ)| * pointHt s v + c * (A.sum fun _ m => |(m : ℝ)|) := by sorry
