-- Prove2me | Theorems.Thm_OrbNetEqui_Equivariance_evNorm_equivariant
-- name    : OrbNetEqui.Equivariance.evNorm_equivariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:06.928522+00:00
-- url     : https://prove2.me/theorems/50c5125a-8919-40b5-9f17-696bf916d9e0
-- title:
--   S2.6, p. 27 — EvNorm (S39): h̄ is invariant and ĥ is equivariant under the unitary representations U^L
-- statement:
--   Let $(U^L)_{L}$ be unitary representations of a group $K$ on $\mathbb V^L=\mathbb C^{\dim L}$, and let $x$ be a feature, i.e. a vector $x_{L,c}\in\mathbb V^L$ for each label $L$ and channel $c$. EvNorm (S39) with statistics $\mu_{L,c},\sigma_{L,c}$, positive scales $\beta_{L,c}>0$ and stability factor $\epsilon>0$ is
--   $$\bar x_{L,c}=\frac{\|x_{L,c}\|-\mu_{L,c}}{\sigma_{L,c}},\qquad \hat x_{L,c,M}=\frac{x_{L,c,M}}{\|x_{L,c}\|+1/\beta_{L,c}+\epsilon},$$
--   with the regularized norm $\|x\|=\sqrt{\sum_M|x_M|^2+\epsilon^2}-\epsilon$ of (23).
--
--   Then for every $k\in K$, writing $(k\cdot x)_{L,c}=U^L_k\,x_{L,c}$,
--   $$\overline{k\cdot x}=\bar x\qquad\text{and}\qquad\widehat{k\cdot x}=k\cdot\hat x.$$
--
--   The invariant part feeds the multilayer perceptrons of the point-wise interaction block, and the equivariant part carries the directions.
--
--   **Formalization Note.** Scalars are complex, so the norm uses $|x_M|^2$. The statistics $\mu,\sigma$ are fixed parameters, so the statement holds for every value of them (batch or layer statistics alike). The page's positivity of $\beta$ and $\epsilon$ is kept as hypotheses. No subgroup restriction is needed, because every $U^L_k$ is unitary.
-- source:
--   Qiao et al., Informing Geometric Deep Learning with Electronic Interactions to Accelerate Quantum Chemistry, arXiv:2105.14655v4, p. 27, S2.6, "Proof of G-equivariance for EvNorm (S39)"; eqs. (22)–(23) p. 9, (S39) p. 26

import Mathlib
import Definitions.Def_OrbNetEqui_Equivariance_Basic

namespace OrbNetEqui.Equivariance

open Matrix

theorem evNorm_equivariant {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ} {nmax : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (μ σ β : Λ → Fin nmax → ℝ) (ε : ℝ) (hβ : ∀ L c, 0 < β L c) (hε : 0 < ε)
    (k : K) (x : Feature Λ dim nmax) :
    evNormBar μ σ ε (featAct U k x) = evNormBar μ σ ε x ∧
      evNormHat β ε (featAct U k x) = featAct U k (evNormHat β ε x) := by sorry

end OrbNetEqui.Equivariance
