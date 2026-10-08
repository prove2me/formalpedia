-- Prove2me | Theorems.Thm_LemkeLCP_Existence_lemma_3
-- name    : LemkeLCP.Existence.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:04:25.376999+00:00
-- url     : https://prove2.me/theorems/c1b68661-4d5a-44d4-ad4f-ee5855504a81
-- title:
--   Lemma 3, p. 7 — a ray of Z* in Z₀* other than E₀*, normalized by eᵀu = 1, satisfies uᵀMu + u₀ = 0
-- statement:
--   Let $M$ be a real square matrix of order $n$ and $q\in\mathbb R^n$, and let $Z_0^*=\{(z,z_0): z\ge0,\ z_0\ge0,\ w=Mz+z_0e-q\ge 0,\ z^{\mathsf T}w=0\}$ be the set (10). Let $\bar z,u\in\mathbb R^n$ and $\bar z_0,u_0\in\mathbb R$ be such that the half-line (15)
--   $$z^*=\bar z^*+\theta u^* = (\bar z+\theta u,\ \bar z_0+\theta u_0),\qquad \theta\ge0,$$
--   lies in $Z_0^*$, and suppose $u$ is normalized by $e^{\mathsf T}u=1$ (in particular $u\ne0$, so the half-line is not the ray $E_0^*$). Then
--   $$u^{\mathsf T}Mu+u_0=0. \tag{20}$$
--
--   This is the key identity behind Theorem 4: under conditions (i)–(ii) on $M$ it forces $u_0=u^{\mathsf T}Mu=0$, from which the proof extracts either an equilibrium point of $Z$ or a certificate that $Z$ is empty.
--
--   **Formalization Note** The ray is given by its parametrization (15). The page also takes $\bar z^*$ to be an extreme point of $Z^*$ and the half-line to be an edge of $Z^*$; these are not assumed here, so the statement is stronger than the page's. "Not the ray $E_0^*$" is the page's Case II, $u\ne 0$, which the normalization $e^{\mathsf T}u=1$ ("We may then take $u$ so that $e^{\mathsf T}u = 1$") implies.
-- source:
--   Lemke, Bimatrix equilibrium points and mathematical programming, hal-01885823v1, p. 7, Lemma 3, (15)–(20)

import Mathlib
import Definitions.Def_LemkeLCP_Existence_Setting
open Matrix

namespace LemkeLCP.Existence

theorem lemma_3 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ι → ℝ)
    (zb u : ι → ℝ) (zb0 u0 : ℝ)
    (hray : ∀ θ : ℝ, 0 ≤ θ → (zb + θ • u, zb0 + θ * u0) ∈ Z0star M q)
    (hu : ∑ i, u i = 1) :
    u ⬝ᵥ (M *ᵥ u) + u0 = 0 := by sorry

end LemkeLCP.Existence
