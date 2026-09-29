-- Prove2me | Theorems.Thm_ModularForm_exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne
-- name    : ModularForm.exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/375de64c-ecce-5713-bd47-48a139a06ffb
-- title:
--   Modular forms on Γ₀(N) separate inequivalent points
-- statement:
--   Let $N$ be a natural number, nonzero, and let $\tau,\tau'$ be points of the complex upper half plane $\mathbb{H}$. Assume that $\tau$ and $\tau'$ lie in distinct orbits of the congruence subgroup $\Gamma_0(N)\subseteq \mathrm{SL}_2(\mathbb{Z})$, in the sense that for every $\gamma\in\Gamma_0(N)$ the image of $\tau$ under the action of $\gamma$ on $\mathbb{H}$ by fractional linear transformations differs from $\tau'$. Then there are an integer $k$ and two modular forms $g,h$ of weight $k$ for $\Gamma_0(N)$ — that is, holomorphic functions on $\mathbb{H}$, invariant under the weight-$k$ slash action of $\Gamma_0(N)$, and of moderate growth at the cusps in Mathlib's sense — whose underlying functions $\mathbb{H}\to\mathbb{C}$ satisfy
--   $$g(\tau)\,h(\tau') \neq g(\tau')\,h(\tau).$$
--   The weight $k$ is produced by the statement and is not prescribed in advance, and the same weight is used for both forms.
--
--   This is the point-separation property of the graded ring of modular forms on $\Gamma_0(N)$: the nonvanishing of the determinant $g(\tau)h(\tau')-g(\tau')h(\tau)$ says that the pair $(g,h)$ assigns distinct points $[g(\tau):h(\tau)]\neq[g(\tau'):h(\tau')]$ of $\mathbb{P}^1(\mathbb{C})$ to $\tau$ and $\tau'$, so that weight-$k$ forms distinguish $\Gamma_0(N)$-inequivalent points of $\mathbb{H}$. It underlies the identification of points of the complex modular curve with $\Gamma_0(N)$-orbits, being used for the criterion [`ModularCurve.ComplexPlaceDictionary.pt_eq_pt_iff`](thm.html#ModularCurve.ComplexPlaceDictionary.pt_eq_pt_iff) and for the corresponding statement [`ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne`](thm.html#ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne) for the subgroups $\Gamma_H(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularForm.exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne (N : ℕ) [NeZero N]
    (τ τ' : ℍ) (hτ : ∀ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • τ ≠ τ') :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k),
      (g : ℍ → ℂ) τ * (h : ℍ → ℂ) τ' ≠ (g : ℍ → ℂ) τ' * (h : ℍ → ℂ) τ := by sorry
