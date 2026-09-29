-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_chart_of_isPivot
-- name    : ModularCurve.JZero.exists_chart_of_isPivot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/99c14825-d841-5502-a894-f984a911c42b
-- title:
--   Uniform non-archimedean disc charts at pivots on X₀(N)
-- statement:
--   Let $N\ge 1$, let $F=\overline{\mathbb Q}$-field `modularFunctionFieldBar N` (the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$, realised inside Laurent series over $\overline{\mathbb Q}$), let $s:\mathrm{Fin}\,r\to F$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and spans the Riemann–Roch space of the divisor `embDivisor N` (the multiple `embDegree N` of the cusp at infinity), and let $p$ be a prime. Then there is $n_0\in\mathbb N$ such that for every non-archimedean absolute value $\mu$ on $\overline{\mathbb Q}$ with $\mu(p)<1$, every place $R$ of $F$ over $\overline{\mathbb Q}$ (a proper valuation subring containing $\overline{\mathbb Q}$ whose ring is a principal ideal ring) and every index $i$ with $\mu(\mathrm{evalVec}\,s\,R\,l)\le\mu(\mathrm{evalVec}\,s\,R\,i)$ for all $l$, there are integers $c_m$ with the following properties. Put $Y_l=s_l/s_i$, $z=\sum_m c_m Y_m$, $t_R=z-z(R)$ where $z(R)=R.\mathrm{evalAt}\,z$, let $\varphi_l\in\overline{\mathbb Q}[[T]]$ have $n$-th coefficient the Taylor coefficient $R.\mathrm{taylorCoeff}\,t_R\,n\,Y_l$, set $\Lambda=n_0\cdot(-\log\mu(p))$, and call a place $w$ a point of the ball if $w=R$ or $\Lambda<\mathrm{prox}_\mu(\mathrm{evalVec}\,s\,R,\mathrm{evalVec}\,s\,w)$, where $\mathrm{prox}_\mu(x,y)=\log\sup_l\mu(x_l)+\log\sup_l\mu(y_l)-\log\sup_{l,m}\mu(x_ly_m-x_my_l)$. Then: (i) every $w$ in the ball satisfies $\mathrm{ord}_w(s_i)\le\mathrm{ord}_w(s_l)$ for all $l$ and $\mathrm{ord}_w(z-z(w))=1$; (ii) $\mu(R.\mathrm{taylorCoeff}\,t_R\,n\,Y_l)\cdot(\mu(p)^{n_0})^n\le 1$ for all $l,n$; (iii) distinct points $w\ne w'$ of the ball have $z(w)\ne z(w')$ and $\mathrm{prox}_\mu(\mathrm{evalVec}\,s\,w,\mathrm{evalVec}\,s\,w')\le-\log\mu(z(w)-z(w'))$; and (iv) for every complete non-trivially normed ultrametric field $L$ and ring homomorphism $\iota:\overline{\mathbb Q}\to L$ with $\|\iota x\|=\mu(x)$, every $w$ in the ball and every $l$, the $\iota$-image of the Taylor series of $Y_l$ at $w$ along $z-z(w)$ is obtained from $\iota_*\varphi_l$ by formal recentring: its $n$-th coefficient equals $\sum_{k}\binom{n+k}{n}\,\mathrm{coeff}_{n+k}(\iota_*\varphi_l)\,\iota(z(w)-z(R))^k$.
--
--   This is the chart-construction step for the non-archimedean local analysis on the modular curve: around each place $R$, with an index $i$ of maximal coordinate size for $\mu$, it produces an integral chart function $z=\sum c_mY_m$ which is a uniformiser at every point of a chordal ball of radius $\mu(p)^{n_0}$ (with $n_0$ independent of $\mu$, $R$ and $i$), together with integrality bounds on the Taylor coefficients, separation and non-contraction of chordal proximity, and compatibility of the Taylor expansions under recentring inside the ball. It is used by [`ModularCurve.JZero.jensen_bad_at_le`](thm.html#ModularCurve.JZero.jensen_bad_at_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_chart_of_isPivot.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.exists_chart_of_isPivot
    (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (p : ℕ) (hp : p.Prime) :
    ∃ n₀ : ℕ, ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      μ (p : AlgebraicClosure ℚ) < 1 →
      ∀ (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (i : Fin r),
        (∀ l, μ (evalVec s R l) ≤ μ (evalVec s R i)) →
      ∃ c : Fin r → ℤ,
        let F   := modularFunctionFieldBar N
        let Y   : Fin r → F := fun l => s l * (s i)⁻¹
        let z   : F := ∑ m, (c m : AlgebraicClosure ℚ) • Y m
        let tR  : F := z - algebraMap _ F (R.evalAt z)
        let φ   : Fin r → PowerSeries (AlgebraicClosure ℚ) :=
                    fun l => PowerSeries.mk fun n => R.taylorCoeff tR n (Y l)
        let Λ   : ℝ := (n₀ : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ)))
        let ball : Place _ F → Prop := fun w => w = R ∨ Λ < prox μ (evalVec s R) (evalVec s w)
        (∀ w, ball w → (∀ l, w.ord (s i) ≤ w.ord (s l)) ∧
                        w.ord (z - algebraMap _ F (w.evalAt z)) = 1) ∧
        (∀ l n, μ (R.taylorCoeff tR n (Y l)) * (μ (p : AlgebraicClosure ℚ) ^ n₀) ^ n ≤ 1) ∧
        (∀ w w', ball w → ball w' → w ≠ w' →
            w.evalAt z ≠ w'.evalAt z ∧
            prox μ (evalVec s w) (evalVec s w') ≤ -Real.log (μ (w.evalAt z - w'.evalAt z))) ∧
        (∀ (L : Type) [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
           (ι : AlgebraicClosure ℚ →+* L), (∀ x, ‖ι x‖ = μ x) →
           ∀ w, ball w → ∀ l,
             PowerSeries.map ι (PowerSeries.mk fun n => w.taylorCoeff (z - algebraMap _ F (w.evalAt z)) n (Y l))
               = (PowerSeries.mk fun n => ∑' k : ℕ,
                    PowerSeries.coeff (n + k) (PowerSeries.map ι (φ l)) * ((n + k).choose n : L)
                      * (ι (w.evalAt z - R.evalAt z)) ^ k)) := by sorry
