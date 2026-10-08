-- Prove2me | Theorems.Thm_HarrisonReimanRBM_Orthant_rescaling_equiv
-- name    : HarrisonReimanRBM.Orthant.rescaling_equiv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:21:51.607232+00:00
-- url     : https://prove2.me/theorems/a679e319-51af-44db-b57b-7b5619d3adc9
-- title:
--   Rescaling: $(y,z)$ solves (5)–(8) for $Q,x$ iff $(y\Lambda,z\Lambda)$ solves (5)–(8) for $\Lambda^{-1}Q\Lambda$, $x\Lambda$
-- statement:
--   Let $K\ge1$, let $Q$ be a nonnegative $K\times K$ matrix with zeros on the diagonal and spectral radius strictly less than unity, and let $\Lambda=\operatorname{diag}(d_1,\dots,d_K)$ with all $d_i>0$. Put $Q^*=\Lambda^{-1}Q\Lambda$. For paths $x,y,z$ on $[0,\infty)$ with values in $\mathbb R^K$ (row vectors), the following are equivalent:
--
--   1. $x\in C_S$ and $y,z\in C$ satisfy (5)–(8) for $Q$ and $x$:
--   $$z(t)=x(t)+y(t)(I-Q),\quad z(t)\ge0,\quad y\text{ nondecreasing},\ y(0)=0,\quad y_j\text{ increases only when }z_j=0;$$
--   2. $x\Lambda\in C_S$ and $y\Lambda,z\Lambda\in C$ satisfy (5)–(8) for $Q^*$ and $x\Lambda$.
--
--   This is the reduction step that, together with Veinott scaling, lets the proof of Theorem 1 assume $\|Q\|<1$.
--
--   **Formalization Note** The paper states it for the $\Lambda$ produced by Veinott scaling; it is stated here for every positive diagonal $\Lambda$, which is the same argument and a stronger statement. (5)–(8) are `Reiman84.QueueLength.IsReflectionPair`, which includes $x\in C_S$ and continuity of $y,z$ on $[0,\infty)$; $y\Lambda$ is the path $t\mapsto y(t)\Lambda$.
-- source:
--   Harrison & Reiman, Reflected Brownian Motion on an Orthant, Ann. Probab. 9(2) (1981), p. 304, proof of Theorem 1, first paragraph

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_HarrisonReimanRBM_Orthant_Basic

namespace HarrisonReimanRBM.Orthant

open Reiman84.QueueLength

/-- Proof of Theorem 1, p. 304: for a diagonal matrix `Λ = diag(d)` with positive diagonal
elements and `Q* = Λ⁻¹QΛ`, two functions `y, z` satisfy (5)–(8) for `Q` and `x` if and only
if `yΛ` and `zΛ` satisfy (5)–(8) for `Q*` and `xΛ`. -/
theorem rescaling_equiv {K : ℕ} (hK : 0 < K) (Q : Matrix (Fin K) (Fin K) ℝ)
    (hQ : IsReflectionMatrix Q) (d : Fin K → ℝ) (hd : ∀ i, 0 < d i)
    (x y z : ℝ → Fin K → ℝ) :
    IsReflectionPair Q x y z ↔
      IsReflectionPair (rescaleMatrix d Q) (scalePath d x) (scalePath d y) (scalePath d z) := by sorry

end HarrisonReimanRBM.Orthant
