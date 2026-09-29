-- Prove2me | Theorems.Thm_ModularCurve_JZero_chowSide_cusp_of_off_support
-- name    : ModularCurve.JZero.chowSide_cusp_of_off_support
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/fa4d9e0b-c411-546a-896a-482cf9a5e089
-- title:
--   Chow side at the cusp from off-support bounds
-- statement:
--   Let $N\ge 1$ and let $\bar F_N$ denote `modularFunctionFieldBar N`, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$ inside Laurent series; write $E = \mathrm{embDegree}\,N \cdot [\bar\infty]$ for `embDivisor N`, where $\bar\infty$ is the place `cuspInftyBar N`. Let $s : \mathrm{Fin}\,r \to \bar F_N$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and its range spans the Riemann–Roch space of $E$ (the functions $f$ with $v(f)\le \exp(E(v))$ at every place $v$), and let $t \in \bar F_N$ have $\mathrm{ord}_{\bar\infty}(t)=1$. Then there is a real constant $C$ such that the following holds for every ring homomorphism $\sigma : \overline{\mathbb Q}\to\mathbb C$, every $k \in \mathbb N$, every nonzero $u$ in the Riemann–Roch space of $k\cdot E$, every divisor $B$ with $B(w) = \mathrm{ord}_w(u) + k\,E(w)$ for all places $w$, and all reals $m, c$: if for every place $v$ with $B(v)=0$ one has $$\bigl|\,\mathrm{chowSide}_{\nu}(s,B,v) - \bigl(k\log \sup_i \nu(\mathrm{evalVec}\,s\,v\,i) - \log \nu(\mathrm{secVal}\,s\,v\,k\,u) - m\bigr)\bigr| \le c\,k,$$ with $\nu(a) = \lVert\sigma a\rVert$, then the same line holds at the cusp for the cycle $B$ with its $\bar\infty$-component erased, with $c$ replaced by $c+C$ and the section value replaced by the regularised value $\mathrm{regVal}\,s\,\bar\infty\,t\,k\,e\,u$, where $e = (B(\bar\infty))^{+}$. Here $\mathrm{evalVec}\,s\,v\,i$ is the value at $v$ of $s_i$ divided by the pivot coordinate, $\mathrm{secVal}\,s\,v\,k\,u$ the value at $v$ of $u$ divided by the $k$-th power of the pivot, $\mathrm{regVal}$ the same quantity further divided by $t^{e}$, and $\mathrm{chowSide}_\nu(s,Z,v) = \sum_w Z_w \log\sup_i \nu(\mathrm{evalVec}\,s\,w\,i) - \log \sup \bigl\{ \nu(\mathrm{chowForm}(s,Z)(a)) / (\sup_i \nu(a_i))^{\sum_w Z_w^{+}} \bigr\}$, the supremum over nonzero $a$ with $\sum_i (\mathrm{evalVec}\,s\,v\,i)\,a_i = 0$.
--
--   This is the transfer, in the archimedean height comparison on the modular curve of level $N$, of the "Chow side equals section line" estimate from places off the support of the section cycle to the base cusp itself, at the cost of an absolute increase $C$ in the slope of the error term and with the section value regularised by a uniformiser at the cusp. It is used by [`ModularCurve.JZero.chowSide_arch_embedding`](thm.html#ModularCurve.JZero.chowSide_arch_embedding).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_chowSide_cusp_of_off_support.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CycleChowForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.chowSide_cusp_of_off_support (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (ht : (cuspInftyBar N).ord t = 1) :
    ∃ C : ℝ, ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (m c : ℝ),
      (∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 →
          |chowSide (fun a => ‖σ a‖) s B v
              - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s v i)‖)
                  - Real.log ‖σ (secVal s v k u)‖ - m)| ≤ c * k) →
      |chowSide (fun a => ‖σ a‖) s (B.erase (cuspInftyBar N)) (cuspInftyBar N)
          - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (cuspInftyBar N) i)‖)
              - Real.log ‖σ (regVal s (cuspInftyBar N) t k (B (cuspInftyBar N)).toNat u)‖ - m)|
        ≤ (c + C) * k := by sorry
