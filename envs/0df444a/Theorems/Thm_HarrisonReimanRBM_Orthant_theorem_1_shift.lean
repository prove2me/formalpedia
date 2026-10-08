-- Prove2me | Theorems.Thm_HarrisonReimanRBM_Orthant_theorem_1_shift
-- name    : HarrisonReimanRBM.Orthant.theorem_1_shift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:22:30.370923+00:00
-- url     : https://prove2.me/theorems/cf6b11fb-885f-448e-8421-d27431734663
-- title:
--   Theorem 1 (11): the shifted triple $(x^*,y^*,z^*)$ again solves (5)–(8)
-- statement:
--   Let $K\ge1$ and let $Q$ be a nonnegative $K\times K$ matrix with zeros on the diagonal and spectral radius strictly less than unity. Fix $x\in C_S$ and $T>0$, and let $(y,z)=(\psi(x),\phi(x))$, i.e. $y,z\in C$ satisfy (5)–(8) for $Q$ and $x$. Define, for $t\ge0$,
--   $$x^*(t)=z(T)+x(T+t)-x(T),\qquad y^*(t)=y(T+t)-y(T),\qquad z^*(t)=z(T+t).$$
--   Then $x^*\in C_S$ and $(y^*,z^*)$ satisfies (5)–(8) for $Q$ and $x^*$. By the uniqueness in Theorem 1, this says $y^*=\psi(x^*)$ and $z^*=\phi(x^*)$.
--
--   This regeneration property is what makes $Z=\phi(X)$ a time-homogeneous Markov process when $X$ is a Brownian motion: after time $T$, the reflected path is the reflection of a path started at $z(T)$.
--
--   **Formalization Note** The conclusion is stated in the pair form "$(y^*,z^*)$ satisfies (5)–(8) for $x^*$", which with the uniqueness part of Theorem 1 (the referenced `Reiman84.QueueLength.lemma_1`) is the paper's "$y^*=\psi(x^*)$, $z^*=\phi(x^*)$"; the paper's proof reduces (11) to exactly this verification. $T>0$ is kept as printed.
-- source:
--   Harrison & Reiman, Reflected Brownian Motion on an Orthant, Ann. Probab. 9(2) (1981), p. 303, Theorem 1, (11)

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_HarrisonReimanRBM_Orthant_Basic

namespace HarrisonReimanRBM.Orthant

open Reiman84.QueueLength

/-- Theorem 1 (11), p. 303: fix `x ∈ C_S`, `T > 0` and `(y, z) = (ψ(x), φ(x))`. With
`x*(t) = z(T) + x(T + t) − x(T)`, `y*(t) = y(T + t) − y(T)` and `z*(t) = z(T + t)`, the pair
`(y*, z*)` satisfies (5)–(8) for `x*`, i.e. `y* = ψ(x*)` and `z* = φ(x*)`. -/
theorem theorem_1_shift {K : ℕ} (hK : 0 < K) (Q : Matrix (Fin K) (Fin K) ℝ)
    (hQ : IsReflectionMatrix Q) (x y z : ℝ → Fin K → ℝ) (h : IsReflectionPair Q x y z)
    (T : ℝ) (hT : 0 < T) :
    IsReflectionPair Q (shiftX T x z) (shiftY T y) (shiftZ T z) := by sorry

end HarrisonReimanRBM.Orthant
