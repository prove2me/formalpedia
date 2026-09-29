-- Prove2me | Theorems.Thm_ModularCurve_sum_ord_jBar_sub_eq_dedekindPsi
-- name    : ModularCurve.sum_ord_jBar_sub_eq_dedekindPsi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/1cd6faac-fa37-5aa9-925c-5d6dc6e75fbe
-- title:
--   Zeros of jmath̄-j₀ on X₀(N) total ψ(N)
-- statement:
--   Fix a natural number $N\neq 0$ and an element $j_0$ of $\overline{\mathbb{Q}}$ (realised as `AlgebraicClosure ℚ`). The field in play is `modularFunctionFieldBar N`, the subfield of the Laurent series field $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of the elements of `modularFunctionFieldFull N`, the latter being the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions attached to $N$; inside it, `jBar N` is the coefficientwise image of the $q$-expansion $j(q)$. A place of this field over $\overline{\mathbb{Q}}$ is a valuation subring, different from the whole field, containing the image of $\overline{\mathbb{Q}}$ and being a principal ideal ring; its degree is the $\overline{\mathbb{Q}}$-dimension of its residue field, and $v.\mathrm{ord}(f)$ is minus the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation of $f$. Assume every such place has degree $1$, and let $S$ be a finite set of places whose members are exactly the places $v$ with $v.\mathrm{ord}\bigl(\mathrm{jBar}\,N-j_0\bigr)>0$. Then $\sum_{v\in S} v.\mathrm{ord}\bigl(\mathrm{jBar}\,N-j_0\bigr)=\psi(N)$, where $\psi(N)=\sum_{d\mid N,\ d\ \text{squarefree}} N/d$ is the Dedekind psi function.
--
--   This is the statement that on the modular curve $X_0(N)$ over $\overline{\mathbb{Q}}$ the divisor of zeros of $\bar\jmath-j_0$ has degree equal to $\psi(N)$, the degree of the covering of the $j$-line; the individual orders (ramification indices above $j_0$) are not identified, and the fibre over $j=\infty$ is not addressed. It feeds the computations of Hecke divisors and of fibres in the characteristic-$p$ model of $X_0(N)$, and the Riemann–Roch estimates used there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sum_ord_jBar_sub_eq_dedekindPsi.lean

import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.sum_ord_jBar_sub_eq_dedekindPsi (N : ℕ) [NeZero N] (j₀ : AlgebraicClosure ℚ)
    (hdeg : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.deg = 1)
    (S : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
    (hS : ∀ v, v ∈ S ↔
      0 < v.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)) :
    ∑ v ∈ S, v.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) =
      dedekindPsi N := by sorry
