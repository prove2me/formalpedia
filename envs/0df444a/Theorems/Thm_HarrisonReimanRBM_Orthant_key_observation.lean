-- Prove2me | Theorems.Thm_HarrisonReimanRBM_Orthant_key_observation
-- name    : HarrisonReimanRBM.Orthant.key_observation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:21:59.821676+00:00
-- url     : https://prove2.me/theorems/e4e4500b-9572-42aa-a4fd-5821a8ce9dad
-- title:
--   Key observation: (5)–(8) are equivalent to (13) $y\in C_0$, (14) $y=\pi(y)$, (15) $z=x+y(I-Q)$
-- statement:
--   Let $K\ge1$ and let $Q$ be a nonnegative $K\times K$ matrix with zeros on the diagonal and spectral radius strictly less than unity. Fix $x\in C_S$ (continuous on $[0,\infty)$ with $x(0)\ge0$) and let $y,z$ be continuous on $[0,\infty)$. Let $\pi$ be the map
--   $$\pi(y)(t)=\sup_{0\le s\le t}\,[y(s)Q-x(s)]^+\quad\text{(componentwise)}.$$
--   Then $(y,z)$ satisfies (5)–(8) for $Q$ and $x$ if and only if
--
--   1. (13) $y\in C_0$: $y$ is nondecreasing with $y(0)=0$;
--   2. (14) $y(t)=\pi(y)(t)$ for all $t\ge0$;
--   3. (15) $z(t)=x(t)+y(t)(I-Q)$ for all $t\ge0$.
--
--   This turns the Skorokhod problem (5)–(8) into a fixed-point equation for $y$ alone, to which the contraction argument is then applied.
--
--   **Formalization Note** The paper proves this after assuming, without loss of generality, that $\|Q\|<1$; the argument does not use that assumption, and it is not made here (a weaker hypothesis, so a stronger statement). Continuity of $y$ and $z$ is assumed on both sides, as the paper's $y,z\in C$; it keeps the suprema in $\pi$ finite. (8) is "$y_j$ is constant on every interval on which $z_j>0$", as in `Reiman84.QueueLength.IsReflectionPair`.
-- source:
--   Harrison & Reiman, Reflected Brownian Motion on an Orthant, Ann. Probab. 9(2) (1981), p. 304, proof of Theorem 1, (12)–(15)

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_HarrisonReimanRBM_Orthant_Basic

namespace HarrisonReimanRBM.Orthant

open Reiman84.QueueLength

/-- Proof of Theorem 1, p. 304, (13)–(15): for `x ∈ C_S` and `y, z` continuous on `[0, ∞)`,
conditions (5)–(8) are equivalent to (13) `y ∈ C₀`, (14) `y = π(y)` and
(15) `z = x + y(I − Q)` (on `t ≥ 0`). -/
theorem key_observation {K : ℕ} (hK : 0 < K) (Q : Matrix (Fin K) (Fin K) ℝ)
    (hQ : IsReflectionMatrix Q) (x y z : ℝ → Fin K → ℝ) (hx : IsCPlus x)
    (hy : ContinuousOn y (Set.Ici 0)) (hz : ContinuousOn z (Set.Ici 0)) :
    IsReflectionPair Q x y z ↔
      (InC0 y ∧ (∀ t, 0 ≤ t → y t = piMap Q x y t) ∧
        ∀ t, 0 ≤ t → z t = x t + Matrix.vecMul (y t) (1 - Q)) := by sorry

end HarrisonReimanRBM.Orthant
