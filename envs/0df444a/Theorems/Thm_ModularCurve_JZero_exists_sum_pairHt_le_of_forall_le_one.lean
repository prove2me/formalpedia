-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_sum_pairHt_le_of_forall_le_one
-- name    : ModularCurve.JZero.exists_sum_pairHt_le_of_forall_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/dd8e9483-a93c-5e7e-a0bc-dac187a0db59
-- title:
--   Pair-height sums bounded by base heights for reduced divisors
-- statement:
--   Fix $N \ge 1$ and work with the function field $\bar F_N :=$ `modularFunctionFieldBar N`, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$ inside Laurent series, with places taken over $\overline{\mathbb Q}$; write $g :=$ `genusFF` $(\overline{\mathbb Q}, \bar F_N)$, the $\overline{\mathbb Q}$-dimension of $H^1(0)$, and $\bar\infty :=$ `cuspInftyBar N`. Let $s : \mathrm{Fin}\,r \to \bar F_N$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and its span is the Riemann–Roch space of `embDivisor N`; here $\mathrm{pointHt}\,s\,v$ is the absolute logarithmic height of the evaluation vector of $s$ at $v$, $\mathrm{pairHt}\,s\,v\,w = \mathrm{pointHt}\,s\,v + \mathrm{pointHt}\,s\,w - h(\mathrm{chordVec}\,s\,v\,w)$, and $\mathrm{baseHt}\,s\,b\,v$ is $0$ for $v = b$ and $\mathrm{pairHt}\,s\,v\,b$ otherwise. Let $\varepsilon > 0$. Then there is a constant $C \in \mathbb R$ such that for every divisor $D$ (a finitely supported $\mathbb Z$-valued function on places) which is effective, has all multiplicities $\le 1$, satisfies $D(\bar\infty) = 0$, has trivial Riemann–Roch space $L(D_{\ne\bar\infty} - \bar\infty) = \bot$ (where $D_{\ne\bar\infty}$ is $D$ with the value at $\bar\infty$ erased, so $D_{\ne\bar\infty} = D$ here), and has $m :=$ `offBaseMass N D` $= \sum_{v \ne \bar\infty} D(v) \ge 2$, one has $$\tfrac12 \sum_{v \ne \bar\infty} \sum_{w \ne v,\bar\infty} D(v)D(w)\,\mathrm{pairHt}\,s\,v\,w \le \sum_{v \ne \bar\infty} \Big((g + m - 2 + \varepsilon)D(v) + (2g-2)\tfrac{D(v)(D(v)-1)}{2}\Big)\,\mathrm{baseHt}\,s\,\bar\infty\,v + C,$$ the sums being over the supports of the indicated finitely supported functions. Since all multiplicities of $D$ are at most $1$, the weights $D(v)(D(v)-1)/2$ vanish.
--
--   This is the reduced (multiplicity-free) case of the lower comparison between the quadratic height form attached to the embedding basis $s$ and the base-height mass of a divisor, written in the grouped-sum shape of the identity relating the two. It is used in the construction of divisor representatives with controlled height form, [`ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm`](thm.html#ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_sum_pairHt_le_of_forall_le_one.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.exists_sum_pairHt_le_of_forall_le_one (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ v, 0 ≤ D v) → (∀ v, D v ≤ 1) → D (cuspInftyBar N) = 0 →
      riemannRochSpace (D.erase (cuspInftyBar N) - Finsupp.single (cuspInftyBar N) (1 : ℤ)) = ⊥ →
      2 ≤ offBaseMass N D →
      ((D.erase (cuspInftyBar N)).sum fun v n => ((D.erase (cuspInftyBar N)).erase v).sum fun w k =>
          (n : ℝ) * (k : ℝ) * pairHt s v w) / 2
        ≤ ((D.erase (cuspInftyBar N)).sum fun v n =>
            (((genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ)
                + (offBaseMass N D : ℝ) - 2 + ε) * (n : ℝ)
              + (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 2)
                * ((n : ℝ) * ((n : ℝ) - 1) / 2)) * baseHt s (cuspInftyBar N) v)
          + C := by sorry
