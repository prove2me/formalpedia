-- Prove2me | Theorems.Thm_ModularForm_exists_gamma_weight_two_forall_tendsto_slash_atImInfty
-- name    : ModularForm.exists_gamma_weight_two_forall_tendsto_slash_atImInfty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/58c494f5-69f3-5e5c-8a32-dcdbee84c8d2
-- title:
--   Weight-two forms on Γ(N) with prescribed cusp values
-- statement:
--   Let $N \geq 1$ be a natural number and let $v \colon \mathrm{SL}_2(\mathbb{Z}) \to \mathbb{C}$ be any function subject to three conditions: first, $v(\gamma \sigma T^j) = v(\sigma)$ for all $\sigma \in \mathrm{SL}_2(\mathbb{Z})$, all $\gamma$ in the principal congruence subgroup $\Gamma(N)$ (`CongruenceSubgroup.Gamma N`) and all $j \in \mathbb{Z}$, where $T = \begin{pmatrix} 1 & 1 \\ 0 & 1\end{pmatrix}$ is `ModularGroup.T`, so that $v$ depends only on the $\Gamma(N)$-orbit of the cusp $\sigma \infty$ together with the $T$-translations; second, $v(-\sigma) = v(\sigma)$; and third, the vanishing relation $\sum_{q} v(\bar q^{\,-1}) = 0$, the (finitely supported) sum being over the coset space $\mathrm{SL}_2(\mathbb{Z})/\Gamma(N)$, with $\bar q$ a chosen representative of $q$. The conclusion is that there exists a modular form $f$ of weight $2$ for $\Gamma(N)$ — holomorphic on the upper half-plane, invariant under the weight-$2$ action of $\Gamma(N)$ and bounded at the cusps in Mathlib's sense — such that for every $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ the slashed function $f \mid_2 \sigma$ tends to $v(\sigma)$ along the filter $\mathrm{Im}\,\tau \to \infty$. Thus the vector of constant terms of $f$ at all cusps realises $v$.
--
--   This is the weight-two case of Hecke's surjectivity theorem for Eisenstein series of level $N$: the map sending a form in $M_2(\Gamma(N))$ to its family of constant terms at the cusps hits exactly the subspace cut out by the single linear relation above. The construction behind it uses the division values $\wp((a_0\tau + a_1)/N; \mathbb{Z}\tau + \mathbb{Z})$ of the Weierstrass function, whose modularity and cusp behaviour are recorded in [`PeriodPair.weierstrassP_torsion_modularForm_slash_tendsto_atImInfty`](thm.html#PeriodPair.weierstrassP_torsion_modularForm_slash_tendsto_atImInfty), together with the inversion identity [`ZMod.exists_sum_units_pi_sq_div_sin_sq_mul_eq`](thm.html#ZMod.exists_sum_units_pi_sq_div_sin_sq_mul_eq) for the values $\pi^2/\sin^2(\pi t/N)$; the result is used to obtain the corresponding statement for $\Gamma_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_gamma_weight_two_forall_tendsto_slash_atImInfty.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm Topology Real Matrix

theorem ModularForm.exists_gamma_weight_two_forall_tendsto_slash_atImInfty (N : ℕ) [NeZero N] (v : SL(2, ℤ) → ℂ)
    (hv : ∀ (σ γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma N → ∀ j : ℤ, v (γ * σ * ModularGroup.T ^ j) = v σ)
    (hneg : ∀ σ : SL(2, ℤ), v (-σ) = v σ)
    (hsum : ∑ᶠ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma N, v q.out⁻¹ = 0) :
    ∃ f : ModularForm (CongruenceSubgroup.Gamma N) 2, ∀ σ : SL(2, ℤ),
      Filter.Tendsto (fun τ => ((⇑f) ∣[(2 : ℤ)] σ) τ) UpperHalfPlane.atImInfty (𝓝 (v σ)) := by sorry
