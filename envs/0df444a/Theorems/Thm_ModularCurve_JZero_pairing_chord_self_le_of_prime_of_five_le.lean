-- Prove2me | Theorems.Thm_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le
-- name    : ModularCurve.JZero.pairing_chord_self_le_of_prime_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/508e8c1c-91d3-51cf-9099-0cc496fad720
-- title:
--   Bounded-mass principal divisors with small self-pairing at every place
-- statement:
--   Let $N$ be a nonzero natural number which is prime with $N \ge 5$, let $\bar F_N =$ `modularFunctionFieldBar N` be the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N$ inside Laurent series, and let $s : \mathrm{Fin}\,r \to \bar F_N$ be an embedding basis in the sense of `IsEmbBasis`, i.e. $s$ is linearly independent over $\overline{\mathbb{Q}}$ and its $\overline{\mathbb{Q}}$-span is the Riemann–Roch space $\{f : v(f) \le \exp(\mathrm{embDivisor}\,N\,(v))\ \text{for all } v\}$ of the divisor `embDivisor N`. Then there exists a real $M$ such that for every $\varepsilon > 0$ there is a real $C$ with: for every place $v$ of $\bar F_N$ over $\overline{\mathbb{Q}}$ (a valuation subring containing the image of $\overline{\mathbb{Q}}$, proper, and a principal ideal ring) there are $g \in \bar F_N$ and a divisor $B$, i.e. a finitely supported integer-valued function on places, such that $B(w) = \mathrm{ord}_w(g)$ for all $w$ — so $B$ is the divisor of $g$ — with $B(v) \ge 1$, with mass $\sum_w |B(w)| \le M$, and with $$\Bigl|\sum_{w \ne v} B(w)\bigl(\beta(w) - \mathrm{pairHt}(v,w)\bigr) + (2\gamma - 1)\,B(v)\,\beta(v)\Bigr| \le \varepsilon\,\mathrm{pt}(v) + C,$$ where $\mathrm{pt} =$ `pointHt s` is the normalised absolute logarithmic height of the pivot-normalised evaluation vector of $s$, $\mathrm{pairHt}(v,w) = \mathrm{pt}(v) + \mathrm{pt}(w) - \mathrm{absLogHeight}(\mathrm{chordVec}\,s\,v\,w)$, $\beta(w) = \mathrm{baseHt}\,s\,(\mathrm{cuspInftyBar}\,N)\,(w)$ equals $0$ if $w$ is the cusp at infinity and $\mathrm{pairHt}(w, \mathrm{cuspInftyBar}\,N)$ otherwise, and $\gamma = \mathrm{genusFF}(\overline{\mathbb{Q}}, \bar F_N)$ is the $\overline{\mathbb{Q}}$-dimension of $H^1$ of the zero divisor. Here the sum over $w \ne v$ is the sum over the support of $B$ with the value at $v$ erased.
--
--   This is the self-pairing estimate entering the construction of the height pairing on the degree-zero divisor class group $\mathrm{JZero}\,N = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \bar F_N)$ of $X_0(N)$: through every place there passes a principal divisor of bounded mass whose associated height-pairing functional at that place is small compared with the point height. It is used by [`ModularCurve.JZero.pairing_principal_le_of_prime_of_five_le`](thm.html#ModularCurve.JZero.pairing_principal_le_of_prime_of_five_le), where the corresponding bound for arbitrary principal divisors is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.lean

import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.pairing_chord_self_le_of_prime_of_five_le (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N)
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        ∃ (g : modularFunctionFieldBar N) (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
          (∀ w, B w = w.ord g) ∧ 1 ≤ B v ∧ (B.sum fun _ m => |(m : ℝ)|) ≤ M ∧
          |((B.erase v).sum fun w m => (m : ℝ) * (baseHt s (cuspInftyBar N) w - pairHt s v w))
              + (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 1)
                * (B v : ℝ) * baseHt s (cuspInftyBar N) v|
            ≤ ε * pointHt s v + C := by sorry
