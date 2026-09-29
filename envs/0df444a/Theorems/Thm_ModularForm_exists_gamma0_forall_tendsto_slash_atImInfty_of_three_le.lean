-- Prove2me | Theorems.Thm_ModularForm_exists_gamma0_forall_tendsto_slash_atImInfty_of_three_le
-- name    : ModularForm.exists_gamma0_forall_tendsto_slash_atImInfty_of_three_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/110374f4-3b71-56a7-86d6-80b0d2566600
-- title:
--   Prescribing constant terms at all cusps of Γ₀(N)
-- statement:
--   Let $N$ be a nonzero natural number and $k$ an integer with $3 \le k$ and $k$ even (so in fact $k \ge 4$). Let $v \colon \mathrm{SL}_2(\mathbb{Z}) \to \mathbb{C}$ be any function satisfying the invariance $v(\gamma \sigma T^{j}) = v(\sigma)$ for all $\sigma, \gamma \in \mathrm{SL}_2(\mathbb{Z})$ with $\gamma$ in the congruence subgroup $\Gamma_0(N)$ and all $j \in \mathbb{Z}$, where $T = \begin{pmatrix} 1 & 1 \\ 0 & 1\end{pmatrix}$ is the generator of the stabiliser of $\infty$; equivalently, $v$ factors through the double coset space $\Gamma_0(N) \backslash \mathrm{SL}_2(\mathbb{Z}) / \langle T \rangle$, i.e. depends only on the cusp $\sigma\infty$ of $\Gamma_0(N)$. The conclusion asserts the existence of a modular form $f$ of weight $k$ for the group $\Gamma_0(N)$ such that for every $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ the function $\tau \mapsto (f \mid[k] \sigma)(\tau)$ on the upper half plane converges to $v(\sigma)$ along the filter $\mathrm{Im}\,\tau \to \infty$. Thus the constant term of $f$ at the cusp $\sigma\infty$ equals the prescribed value $v(\sigma)$.
--
--   This is the surjectivity of the constant-term (value-at-the-cusps) map $M_k(\Gamma_0(N)) \to \mathbb{C}^{\{\text{cusps}\}}$ for even weight $k \ge 4$, classically obtained from the weight-$k$ Eisenstein series attached to $\Gamma_0(N)$-orbits of vectors of order $N$ in $(\mathbb{Z}/N)^2$. It is used in the construction of modular forms with prescribed cocycle behaviour, namely in [`HeckeEis.exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles`](thm.html#HeckeEis.exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_gamma0_forall_tendsto_slash_atImInfty_of_three_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm Topology

theorem ModularForm.exists_gamma0_forall_tendsto_slash_atImInfty_of_three_le (N : ℕ) [NeZero N] (k : ℤ)
    (hk : 3 ≤ k) (hke : Even k) (v : SL(2, ℤ) → ℂ)
    (hv : ∀ (σ γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N → ∀ j : ℤ, v (γ * σ * ModularGroup.T ^ j) = v σ) :
    ∃ f : ModularForm (CongruenceSubgroup.Gamma0 N) k, ∀ σ : SL(2, ℤ),
      Filter.Tendsto (fun τ => ((⇑f) ∣[k] σ) τ) UpperHalfPlane.atImInfty (𝓝 (v σ)) := by sorry
