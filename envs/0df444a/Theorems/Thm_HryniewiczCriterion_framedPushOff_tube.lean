-- Prove2me | Theorems.Thm_HryniewiczCriterion_framedPushOff_tube
-- name    : HryniewiczCriterion.framedPushOff_tube
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T22:18:10.517011+00:00
-- url     : https://prove2.me/theorems/4e20b1fc-6e5d-46e2-bfeb-aa700c95289e
-- title:
--   Small push-offs of a framed loop in $S^3$ along its frame miss the loop (tube lemma)
-- statement:
--   Let $\gamma:\mathbb{R}\to S^3\subset\mathbb{R}^4$ be a $C^2$ loop, $\gamma(s+1)=\gamma(s)$, injective modulo $1$. Let $e_1,e_2$ be continuous $1$-periodic vector fields along $\gamma$ with
--   $$\det\big(\gamma(s),\gamma'(s),e_1(s),e_2(s)\big)>0\quad\text{for all } s.$$
--   Fix $0<a\le b$. Then there is $\varepsilon_0>0$ such that for $0<\varepsilon<\varepsilon_0$, all $s,t,\varphi$ and all $\rho\in[a,b]$, the vector $x=\gamma(t)+\varepsilon\rho\,(\cos\varphi\,e_1(t)+\sin\varphi\,e_2(t))$ is non-zero and is not a positive multiple of $\gamma(s)$. Equivalently, the radially normalized push-off $x/|x|$ misses the loop.
--
--   Proof: write $s=t+h+n$ with $n\in\mathbb{Z}$, $|h|\le\frac12$, and suppose $x=\mu\gamma(t+h)$, $\mu>0$; then $|\mu-1|=O(\varepsilon)$. If $|h|\ge\eta$, injectivity and compactness bound $|\gamma(t+h)-\gamma(t)|$ below, which is impossible. If $|h|<\eta$, write $\gamma(t+h)=\gamma(t)+h\gamma'(t)+T$ with $|T|\le Lh^2$. Pairing with $\gamma'(t)$, using $\gamma\perp\gamma'$, gives $|h|=O(\varepsilon)$. The determinant $\det(\gamma,\gamma',\cdot,-\sin\varphi\,e_1+\cos\varphi\,e_2)$ then gives $\varepsilon\rho\det(\gamma,\gamma',e_1,e_2)=\mu\det(\gamma,\gamma',T,\cdot)=O(\varepsilon^2)$, a contradiction for small $\varepsilon$.
-- source:
--   Tubular neighbourhood of an embedded loop; D. Rolfsen, Knots and Links, Publish or Perish, 1976, Ch. 5D (linking number via the Gauss integral; a meridian links its knot once; framings and the twisting of push-offs); used for self-linking numbers in U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Definition 1.5.

import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.framedPushOff_tube (γ e₁ e₂ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (he₁ : Continuous e₁)
    (he₂ : Continuous e₂) (hγper : ∀ s, γ (s + 1) = γ s) (he₁per : ∀ s, e₁ (s + 1) = e₁ s)
    (he₂per : ∀ s, e₂ (s + 1) = e₂ s) (hγunit : ∀ s, euclidNorm (γ s) = 1)
    (hinj : ∀ s t, γ s = γ t → ∃ n : ℤ, t = s + n)
    (hdet : ∀ s, 0 < Matrix.det (Matrix.of ![γ s, deriv γ s, e₁ s, e₂ s]))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ s t ρ φ : ℝ, a ≤ ρ → ρ ≤ b →
      γ t + ε • (ρ • (Real.cos φ • e₁ t + Real.sin φ • e₂ t)) ≠ 0 ∧
      ∀ μ : ℝ, 0 < μ → γ t + ε • (ρ • (Real.cos φ • e₁ t + Real.sin φ • e₂ t)) ≠ μ • γ s := by sorry
