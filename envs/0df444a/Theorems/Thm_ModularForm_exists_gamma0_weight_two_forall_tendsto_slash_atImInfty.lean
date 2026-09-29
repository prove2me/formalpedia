-- Prove2me | Theorems.Thm_ModularForm_exists_gamma0_weight_two_forall_tendsto_slash_atImInfty
-- name    : ModularForm.exists_gamma0_weight_two_forall_tendsto_slash_atImInfty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/b690560f-4c62-5897-81f8-ad5277da6cc2
-- title:
--   Weight-two forms on Γ₀(N) with prescribed cusp values
-- statement:
--   Let $N$ be a positive natural number and let $v\colon \mathrm{SL}_2(\mathbb Z)\to\mathbb C$ be any function subject to two hypotheses. First, $v$ is invariant in the sense that $v(\gamma\sigma T^{j})=v(\sigma)$ for all $\sigma\in\mathrm{SL}_2(\mathbb Z)$, all $\gamma$ in the congruence subgroup $\Gamma_0(N)$ and all $j\in\mathbb Z$, where $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$; thus $v$ depends only on the double coset $\Gamma_0(N)\sigma\langle T\rangle$, i.e. only on the cusp $\sigma\infty$ of $\Gamma_0(N)$. Second, $v$ satisfies the residue relation that the (finite) sum of $v(q^{-1})$, as $q$ runs over chosen representatives of the coset space $\mathrm{SL}_2(\mathbb Z)/\Gamma_0(N)$, vanishes; the first hypothesis makes each summand independent of the representative, and grouped by cusps this sum is $\sum_c h_c v(c)$ with $h_c$ the width of $c$. The conclusion is that there exists a modular form $f$ of weight $2$ for the subgroup $\Gamma_0(N)$ such that for every $\sigma\in\mathrm{SL}_2(\mathbb Z)$ the slashed function $f\mid[2]\sigma$ tends to $v(\sigma)$ as $\operatorname{Im}\tau\to\infty$. Unlike the corresponding statement for $\Gamma(N)$, no hypothesis $v(-\sigma)=v(\sigma)$ is needed.
--
--   This is the weight-two case of the classical description of the Eisenstein space of $\Gamma_0(N)$: the constant terms at the cusps of forms in $M_2(\Gamma_0(N))$ realise exactly the hyperplane cut out by the residue relation $\sum_c h_c v(c)=0$, the Eisenstein series being produced by Hecke's limiting process since $\sum (c\tau+d)^{-2}$ is not absolutely convergent. It is obtained here from the analogous statement for the principal congruence subgroup $\Gamma(N)$, and is used in the construction of modular forms attached to cocycles in [`HeckeEis.exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles`](thm.html#HeckeEis.exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_gamma0_weight_two_forall_tendsto_slash_atImInfty.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm Topology

theorem ModularForm.exists_gamma0_weight_two_forall_tendsto_slash_atImInfty (N : ℕ) [NeZero N] (v : SL(2, ℤ) → ℂ)
    (hv : ∀ (σ γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N → ∀ j : ℤ, v (γ * σ * ModularGroup.T ^ j) = v σ)
    (hsum : ∑ᶠ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, v q.out⁻¹ = 0) :
    ∃ f : ModularForm (CongruenceSubgroup.Gamma0 N) 2, ∀ σ : SL(2, ℤ),
      Filter.Tendsto (fun τ => ((⇑f) ∣[(2 : ℤ)] σ) τ) UpperHalfPlane.atImInfty (𝓝 (v σ)) := by sorry
