-- Prove2me | Theorems.Thm_ModularCurve_JZero_prox_sum_chowSide
-- name    : ModularCurve.JZero.prox_sum_chowSide
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/fae11ea2-9426-5212-9c1e-a9de53c19c87
-- title:
--   Chordal proximity sums agree with the Chow side up to O(k)
-- statement:
--   Fix $N\ge 1$ and a family $s\colon \mathrm{Fin}\,r\to$ `modularFunctionFieldBar N` (the base change to $\overline{\mathbb{Q}}=$ `AlgebraicClosure ℚ` of the full level-$N$ modular function field, realised inside Laurent series) which is an `IsEmbBasis`, i.e. $s$ is linearly independent over $\overline{\mathbb{Q}}$ and spans the Riemann–Roch space $\{f : v(f)\le \exp(D(v))\ \forall v\}$ of the divisor `embDivisor N` $=\mathrm{embDegree}(N)\cdot[\infty]$ supported at the cusp `cuspInftyBar N`. Then there is a real constant $c$ — depending only on $N$ and $s$ — with the following property. Let $\sigma\colon\overline{\mathbb{Q}}\to\mathbb{C}$ be a ring homomorphism, put $\nu(a)=\|\sigma a\|$, let $k\in\mathbb{N}$, let $u\ne 0$ lie in the Riemann–Roch space of $k\cdot$`embDivisor N`, and let $B$ be a divisor with $B(w)=\operatorname{ord}_w(u)+k\cdot(\mathrm{embDivisor}\,N)(w)$ at every place $w$. Write $\mathrm{prox}(\nu,x,y)=\log\sup_i\nu(x_i)+\log\sup_i\nu(y_i)-\log\sup_{i,j}\nu(x_iy_j-x_jy_i)$ and, for a place $v$, $x(v)=$ `evalVec s v`, the vector of residues at $v$ of the $s_i$ normalised by a pivot coordinate; and $\mathrm{chowSide}(\nu,s,Z,v)=\sum_w Z(w)\log\sup_i\nu(x(w)_i)-\mathrm{chowLogAt}(\nu,s,Z,v)$, where $\mathrm{chowLogAt}$ is the logarithm of the supremum of $\nu(\mathrm{chowForm}(s,Z)(a))/(\sup_i\nu(a_i))^{\deg Z}$ over nonzero covectors $a$ annihilating $x(v)$, with $\deg Z=\sum_w Z(w)^+$. The conclusion asserts two bounds: first, with the cusp removed from $B$, $$\Big|\sum_{w}(B\setminus[\infty])(w)\,\mathrm{prox}(\nu,x(\infty),x(w))-\mathrm{chowSide}(\nu,s,B\setminus[\infty],\infty)\Big|\le ck;$$ second, for every place $v$ with $B(v)=0$, $\big|\sum_w B(w)\,\mathrm{prox}(\nu,x(v),x(w))-\mathrm{chowSide}(\nu,s,B,v)\big|\le ck$.
--
--   This is the archimedean comparison between the chordal-proximity sum of a section's divisor and the Chow-form expression attached to the same cycle, the two differing by at most a constant multiple of the degree parameter $k$; it is the quantitative input for the archimedean local height on $\mathrm{Pic}^0$ of the modular curve. It is used by [`ModularCurve.JZero.chowSide_cusp_of_off_support`](thm.html#ModularCurve.JZero.chowSide_cusp_of_off_support), [`ModularCurve.JZero.jensen_arch_embedding`](thm.html#ModularCurve.JZero.jensen_arch_embedding) and [`ModularCurve.JZero.prox_sum_le_of_forall_log_secVal_le`](thm.html#ModularCurve.JZero.prox_sum_le_of_forall_log_secVal_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_prox_sum_chowSide.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CycleChowForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.prox_sum_chowSide (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c : ℝ, ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
        |((B.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) *
            prox (fun a => ‖σ a‖) (evalVec s (cuspInftyBar N)) (evalVec s w))
            - chowSide (fun a => ‖σ a‖) s (B.erase (cuspInftyBar N)) (cuspInftyBar N)| ≤ c * k ∧
        ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 →
          |(B.sum fun w n => (n : ℝ) * prox (fun a => ‖σ a‖) (evalVec s v) (evalVec s w))
              - chowSide (fun a => ‖σ a‖) s B v| ≤ c * k := by sorry
