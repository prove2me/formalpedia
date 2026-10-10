-- Prove2me | Theorems.Thm_NonconvexDRS_DRS_theorem_4_1
-- name    : NonconvexDRS.DRS.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:46:17.137251+00:00
-- url     : https://prove2.me/theorems/d83b57ef-b1da-48b6-9043-31eade474e2a
-- title:
--   Theorem 4.1, p. 10 — sufficient decrease φ^DR_γ(s) − φ^DR_γ(s⁺) ≥ c/(1+γL)²·‖s − s⁺‖² with c > 0, constants as derived in the proof
-- statement:
--   Suppose Assumption I holds: $\varphi_1$ is $L$-smooth and $\sigma$-hypoconvex with $\sigma\in[-L,L]$ ($L>0$), $\varphi_2$ is proper and lsc, and $\varphi=\varphi_1+\varphi_2$ has a minimizer. Write $p=\sigma/L$. Consider one DRS update $s\mapsto(u,v,s^+)$ with stepsize $\gamma>0$ and relaxation $\lambda$: $u\in\operatorname{prox}_{\gamma\varphi_1}(s)$, $v\in\operatorname{prox}_{\gamma\varphi_2}(2u-s)$, $s^+=s+\lambda(v-u)$.
--
--   1. If $\lambda\in(0,2)$ and $\gamma<\min\{\frac{2-\lambda}{2[\sigma]_-},\frac1L\}$, then
--   $$\varphi^{\mathrm{DR}}_\gamma(s)-\varphi^{\mathrm{DR}}_\gamma(s^+)\ge\frac{c}{(1+\gamma L)^2}\|s-s^+\|^2\tag{4.2}$$
--   with the strictly positive constant
--   $$c=\frac{2-\lambda}{2\lambda\gamma}-\begin{cases}L\max\Big\{\frac{[p]_-}{2(1-[p]_-)},\ \frac{\gamma L}{\lambda}-\frac12\Big\}&\text{if }p\ge\frac\lambda2-1,\\[2pt]\frac{[\sigma]_-}{\lambda}&\text{otherwise.}\end{cases}$$
--   2. If $\varphi_1$ is strongly convex ($\sigma>0$), then (4.2) also holds for
--   $$2\le\lambda<\frac4{1+\sqrt{1-p}}\qquad\text{and}\qquad\frac{p\lambda-\delta}{4\sigma}<\gamma<\frac{p\lambda+\delta}{4\sigma},\qquad\delta=\sqrt{(p\lambda)^2-8p(\lambda-2)},$$
--   with the strictly positive constant $c=\frac{2-\lambda}{2\lambda\gamma}+\sigma\big(\frac12-\frac{\gamma L}{\lambda}\big)$.
--
--   The page states (4.3) with $\frac12-\frac{\gamma L}{\lambda}$ as the second entry of the max, and (4.5) as $c=\frac{2-\lambda}{2\lambda\gamma}+\frac{\sigma}{\lambda}\big(\frac12-\frac{\gamma L}{\lambda}\big)$. This is the engine of the convergence analysis: the envelope decreases by a fixed multiple of the squared step.
--
--   **Formalization Note** Both printed constants are corrected to the values the proof derives. (a) In (4.3) the proof's Case 1a, (4.8) p. 11, gives $c/L=\frac{2-\lambda}{2\lambda\gamma L}+\min\{\frac{p}{2(1+p)},\frac12-\frac{\gamma L}{\lambda}\}$, i.e. the entry $\frac{\gamma L}{\lambda}-\frac12$ inside $-L\max$. The printed version is false: for $\varphi_1(x)=\frac L2x^2$ on $\mathbb R$, $\varphi_2\equiv0$, $\lambda=1$, $\gamma L=0.9$, the printed $c=L/1.8$ violates (4.2) while the corrected $c=L(1/1.8-0.4)$ satisfies it. (b) In (4.5) the proof's (4.10), p. 12, gives $c=L\big(\frac{2-\lambda}{2\lambda\gamma L}+\frac{(\lambda-2\gamma L)p}{2\lambda}\big)=\frac{2-\lambda}{2\lambda\gamma}+\sigma(\frac12-\frac{\gamma L}\lambda)$, consistent with Remark 4.2's row $\lambda=2$, $c=\frac{\sigma}{2}(1-\gamma L)$; the printed $\frac\sigma\lambda$ makes $c$ negative at $\sigma=L$, $\lambda=3$, $\gamma L=0.75$, inside (4.4). Reciprocal bounds are multiplied out ($\gamma L<1$, $2\gamma[\sigma]_-<2-\lambda$, and (4.4) multiplied by $4\sigma>0$). (4.2) is written in `EReal` without subtraction. In case (4.4) no bound $\gamma L<1$ is added: it follows from (4.4). $L>0$ is the mission's standing addition.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 10, Theorem 4.1, (4.2)–(4.5); constants corrected per the proof, (4.8) p. 11 and (4.10) p. 12

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_DRS_Setting

open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace

namespace NonconvexDRS.DRS

/-- Theorem 4.1 (Sufficient decrease on the DRE), p. 10, with the constants (4.3) and
(4.5) as derived in its proof ((4.8) p. 11 and (4.10) p. 12). -/
theorem theorem_4_1 {p : ℕ} (φ₁ : EuclideanSpace ℝ (Fin p) → ℝ) (φ₂ : EuclideanSpace ℝ (Fin p) → EReal)
    (L σ : ℝ) (hL : 0 < L) (hσ : -L ≤ σ ∧ σ ≤ L)
    (hsmooth : IsLSmooth φ₁ L) (hhypo : IsHypoconvex φ₁ σ)
    (hprop : IsProper φ₂) (hlsc : LowerSemicontinuous φ₂)
    (hsol : ∃ xs, ∀ x, (φ₁ xs : EReal) + φ₂ xs ≤ (φ₁ x : EReal) + φ₂ x)
    (γ lam : ℝ) (hγ : 0 < γ) (s u v splus : EuclideanSpace ℝ (Fin p))
    (hu : u ∈ proxSet (fun x => (φ₁ x : EReal)) γ s)
    (hv : v ∈ proxSet φ₂ γ ((2 : ℝ) • u - s))
    (hsplus : splus = s + lam • (v - u)) :
    (0 < lam → lam < 2 → γ * L < 1 → 2 * γ * negPartR σ < 2 - lam →
      0 < cDR L σ γ lam ∧
      dre φ₁ φ₂ γ splus + ((cDR L σ γ lam / (1 + γ * L) ^ 2 * ‖s - splus‖ ^ 2 : ℝ) : EReal)
        ≤ dre φ₁ φ₂ γ s) ∧
    (0 < σ → 2 ≤ lam → lam * (1 + Real.sqrt (1 - σ / L)) < 4 →
      σ / L * lam - deltaDR L σ lam < 4 * σ * γ → 4 * σ * γ < σ / L * lam + deltaDR L σ lam →
      0 < cDRsc L σ γ lam ∧
      dre φ₁ φ₂ γ splus + ((cDRsc L σ γ lam / (1 + γ * L) ^ 2 * ‖s - splus‖ ^ 2 : ℝ) : EReal)
        ≤ dre φ₁ φ₂ γ s) := by sorry

end NonconvexDRS.DRS
