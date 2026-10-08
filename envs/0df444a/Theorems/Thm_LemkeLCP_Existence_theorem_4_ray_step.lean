-- Prove2me | Theorems.Thm_LemkeLCP_Existence_theorem_4_ray_step
-- name    : LemkeLCP.Existence.theorem_4_ray_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:04:30.063539+00:00
-- url     : https://prove2.me/theorems/36512a26-0a1f-4959-924e-9af60d06191e
-- title:
--   (22)–(25), proof of Theorem 4, pp. 7–8 — under (i)–(ii) a ray of Z* in Z₀* starts at an equilibrium point of Z, or Z is empty
-- statement:
--   Let $M$ be a real square matrix of order $n$ satisfying conditions (i)–(ii) of Theorem 4: for every $u\ge 0$, $u^{\mathsf T}Mu\ge 0$, and $u^{\mathsf T}Mu=0$ implies $Mu+M^{\mathsf T}u=0$. Let $q\in\mathbb R^n$, and let $\bar z,u\in\mathbb R^n$, $\bar z_0,u_0\in\mathbb R$ be such that the half-line
--   $$(\bar z+\theta u,\ \bar z_0+\theta u_0),\qquad\theta\ge 0,$$
--   lies in $Z_0^*$ (the set (10)), with $e^{\mathsf T}u=1$. Then exactly as in (22)–(25) one of the following holds:
--
--   1. $\bar z_0=0$ and $\bar z$ is an equilibrium point of $Z=\{z\ge0: Mz-q\ge0\}$; or
--   2. $\bar z_0>0$ and $Z$ is empty.
--
--   This is the step that turns the end of Lemke's augmented path into the conclusion of Theorem 4: a ray of $Z^*$ in $Z_0^*$ other than $E_0^*$ either starts at an equilibrium point of $Z$, or produces a vector $u\ge0$ with $M^{\mathsf T}u\le0$, $u^{\mathsf T}q>0$, which makes $Z$ empty by Lemma 2 (p. 4) (called "Lemma 1" on p. 8).
--
--   **Formalization Note** The ray is given by its parametrization (15), with no assumption that $\bar z^*$ is an extreme point of $Z^*$ or that the half-line is an edge; the statement is therefore stronger than the page's setting.
-- source:
--   Lemke, Bimatrix equilibrium points and mathematical programming, hal-01885823v1, pp. 7–8, proof of Theorem 4, (22)–(25)

import Mathlib
import Definitions.Def_LemkeLCP_Existence_Setting
open Matrix

namespace LemkeLCP.Existence

theorem theorem_4_ray_step {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (q : ι → ℝ) (hM : CopositivePlus M)
    (zb u : ι → ℝ) (zb0 u0 : ℝ)
    (hray : ∀ θ : ℝ, 0 ≤ θ → (zb + θ • u, zb0 + θ * u0) ∈ Z0star M q)
    (hu : ∑ i, u i = 1) :
    (zb0 = 0 ∧ IsEquilibriumPoint M q zb) ∨ (0 < zb0 ∧ Z M q = ∅) := by sorry

end LemkeLCP.Existence
