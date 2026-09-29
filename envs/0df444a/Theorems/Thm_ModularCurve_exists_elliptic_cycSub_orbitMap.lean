-- Prove2me | Theorems.Thm_ModularCurve_exists_elliptic_cycSub_orbitMap
-- name    : ModularCurve.exists_elliptic_cycSub_orbitMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/8e627a00-a37e-5883-bb5b-3a4df6f1fea6
-- title:
--   Places above j₀ and orbits of cyclic N-subgroups
-- statement:
--   Let $N$ be a positive natural number and let $j_0$ be an element of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. The assertion is that there exist a Weierstrass curve $E_0$ over $\overline{\mathbb{Q}}$ which is elliptic (its discriminant is invertible) and has $j$-invariant $j_0$, and a map $f$ from `CycSub E₀ N`, the set of subgroups of the group of affine points of $E_0$ of the form $\langle g\rangle$ for some point $g$ of additive order exactly $N$, to the set of those places $w$ of the extension $\overline{\mathbb{Q}} \subseteq$ `modularFunctionFieldBar N` — a valuation subring, not the whole field, containing the constants and a principal ideal ring — at which $\operatorname{ord}_w(\bar\jmath_N - j_0) > 0$, where `modularFunctionFieldBar N` is the subfield of $\overline{\mathbb{Q}}$-Laurent series generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of the level-$N$ divisor expansions, $\bar\jmath_N$ is the coefficientwise image of the $q$-expansion of $j$, and $\operatorname{ord}_w$ is minus the logarithm of the associated height-one-spectrum valuation. The map $f$ satisfies: $f(H) = f(H')$ holds if and only if `SameOrbit E₀ H H'`, i.e. there is a variable change $\gamma$ fixing $E_0$ and generators $g$ of $H$, $g'$ of $H'$ with $g'$ the image of $g$ under the induced map `Point.vcInvFun` on points; and for every such place $w$ the natural number $\operatorname{ord}_w(\bar\jmath_N - j_0)$ equals the cardinality of the fibre $f^{-1}(w)$.
--
--   This is the local comparison, above a single value $j_0$ of the $j$-line, between the places of the level-$N$ modular function field over $\overline{\mathbb{Q}}$ and the orbits of cyclic subgroups of order $N$ on an elliptic curve with $j$-invariant $j_0$, the order of vanishing of $j - j_0$ at a place matching the size of the corresponding orbit. It is used in the proof of [`ModularCurve.emd_holds`](thm.html#ModularCurve.emd_holds) and of [`ModularCurve.ord_jBar_sub_eq_one_of_ne_zero_of_ne`](thm.html#ModularCurve.ord_jBar_sub_eq_one_of_ne_zero_of_ne), which extracts unramifiedness away from the exceptional $j$-invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_elliptic_cycSub_orbitMap.lean

import Definitions.Def_ModularCurve_EMD
import Definitions.Def_ModularCurve_MazurStepThreeInputs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.exists_elliptic_cycSub_orbitMap (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ) :
    ∃ (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) (_ : E₀.IsElliptic), E₀.j = j₀ ∧
      ∃ f : CycSub E₀ N →
          {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
            0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)},
        (∀ H H' : CycSub E₀ N, f H = f H' ↔ SameOrbit E₀ H.1 H'.1) ∧
        ∀ w : {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
            0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)},
          ((w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).ord
              (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)).toNat =
            Nat.card {H : CycSub E₀ N // f H = w} := by sorry
