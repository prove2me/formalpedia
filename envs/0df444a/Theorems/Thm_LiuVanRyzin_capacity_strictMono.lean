-- Prove2me | Theorems.Thm_LiuVanRyzin_capacity_strictMono
-- name    : LiuVanRyzin.capacity_strictMono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:37:28.849087+00:00
-- url     : https://prove2.me/theorems/6b82fb11-1865-47bb-867c-eeffbed91580
-- title:
--   Proposition 5 — capacity $C(v)$ and fill rate $q(v)$ strictly increase in the cutoff $v$
-- statement:
--   Assume valuations uniform on $[0,\bar U]$ with $\bar U>0$, market size $N>0$, prices $p_2<p_1$ and power utility $x^\gamma$ with $0<\gamma<1$. For a cutoff $v\in[p_1,\bar U]$ let
--   $$q(v)=\left(\frac{v-p_1}{v-p_2}\right)^\gamma,\qquad C(v)=\frac{N}{\bar U}\bigl(\bar U-v+(v-p_2)q(v)\bigr).$$
--   Then both $C$ and $q$ are strictly increasing on $[p_1,\bar U]$. Consequently $C$ is strictly increasing in the fill rate as well: for $v,w\in[p_1,\bar U]$, $q(v)<q(w)$ implies $C(v)<C(w)$.
--
--   This is what makes the reduction of the firm's problem (4)–(5) to the single-variable problem (6) legitimate: choosing a stocking quantity is the same as choosing a cutoff or a fill rate.
--
--   **Formalization Note** "Increases" is read as strictly increasing. The statement is restricted to $[p_1,\bar U]$, the range of (5).
-- source:
--   Liu, van Ryzin, Strategic Capacity Rationing to Induce Early Purchases, Management Science 54(6):1115–1131 (2008), p. 1123, Proposition 5

import Mathlib
import Definitions.Def_LiuVanRyzin_PowerModel

namespace LiuVanRyzin

/-- Proposition 5 (Liu–van Ryzin 2008, p. 1123). Under the uniform law on `[0, Ū]` and the
power utility `x ^ γ`, on `p₁ ≤ v ≤ Ū` the capacity `C(v)` is strictly increasing in the cutoff
`v`, and so is the fill rate `q(v)`; hence `C` is strictly increasing in `q` as well. -/
theorem capacity_strictMono (N Ubar p₁ p₂ γ : ℝ) (hN : 0 < N) (hU : 0 < Ubar)
    (hp : p₂ < p₁) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    StrictMonoOn (capacity N Ubar p₁ p₂ γ) (Set.Icc p₁ Ubar) ∧
      StrictMonoOn (fillRate p₁ p₂ γ) (Set.Icc p₁ Ubar) := by sorry

end LiuVanRyzin
