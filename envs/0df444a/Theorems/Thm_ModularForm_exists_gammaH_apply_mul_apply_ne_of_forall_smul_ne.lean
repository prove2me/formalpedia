-- Prove2me | Theorems.Thm_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne
-- name    : ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/eb5513cc-c056-523f-b76c-107c89d2004f
-- title:
--   Forms on Γ_H(N) separate inequivalent points
-- statement:
--   Let $N$ be a nonzero natural number and let $H$ be a subgroup of $(\mathbb{Z}/N)^\times$. Write $\Gamma_H(N)$ for the subgroup [`CohCarrier.GammaH N H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image under the inclusion $\Gamma_0(N)\hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism [`CohCarrier.gamma0Units`](def/CohCarrier_Level.html#L121) sending a matrix of $\Gamma_0(N)$ to the unit of $\mathbb{Z}/N$ with value its lower-right entry modulo $N$ and inverse its upper-left entry modulo $N$; thus $\Gamma_H(N)$ consists of the matrices $\begin{pmatrix} a & b \\ c & d\end{pmatrix}\in\mathrm{SL}_2(\mathbb{Z})$ with $c\equiv 0 \pmod N$ and $d \bmod N \in H$. Let $\tau,\tau'$ be points of the upper half plane and assume that $\gamma\cdot\tau \neq \tau'$ for every $\gamma \in \Gamma_H(N)$, i.e. $\tau$ and $\tau'$ lie in distinct $\Gamma_H(N)$-orbits. Then there are an integer $k$ and two modular forms $g,h$ of weight $k$ for the image of $\Gamma_H(N)$ in $\mathrm{GL}_2(\mathbb{R})$ such that, for the underlying functions on the upper half plane,
--   $$g(\tau)\,h(\tau') \neq g(\tau')\,h(\tau).$$
--
--   This is the separation-of-points property of the graded ring of modular forms on $\Gamma_H(N)$: the linear systems of weight-$k$ forms distinguish distinct points of the open modular curve $Y_H(N) = \Gamma_H(N)\backslash\mathfrak{H}$. It is used in the construction of the complex-analytic description of the modular curve, where it supplies the injectivity criterion for points recorded in [`ModularCurve.ComplexPlaceDictionaryOf.pt_eq_pt_iff_gammaH`](thm.html#ModularCurve.ComplexPlaceDictionaryOf.pt_eq_pt_iff_gammaH).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne.lean

import Mathlib
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne (N : ℕ) [NeZero N]
    (H : Subgroup (ZMod N)ˣ) (τ τ' : UpperHalfPlane)
    (hτ : ∀ γ ∈ CohCarrier.GammaH N H, γ • τ ≠ τ') :
    ∃ (k : ℤ) (g h : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k),
      (g : UpperHalfPlane → ℂ) τ * (h : UpperHalfPlane → ℂ) τ' ≠
        (g : UpperHalfPlane → ℂ) τ' * (h : UpperHalfPlane → ℂ) τ := by sorry
