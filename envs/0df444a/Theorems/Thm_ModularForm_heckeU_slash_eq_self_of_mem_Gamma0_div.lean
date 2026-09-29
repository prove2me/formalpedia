-- Prove2me | Theorems.Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0_div
-- name    : ModularForm.heckeU_slash_eq_self_of_mem_Gamma0_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/b79565f9-deb6-59d8-966b-16d77848b707
-- title:
--   Uₚ lowers the level from Γ₀(N) to Γ₀(N/p) when p² ∣ N
-- statement:
--   Fix a natural number $N$, an integer weight $k$ and a natural number $p$ with $p^2 \mid N$ (no primality or positivity of $p$ is assumed). Let $f : \mathbb{H} \to \mathbb{C}$ be a function on the upper half-plane that is invariant under the weight-$k$ slash action of the congruence subgroup $\Gamma_0(N)$, viewed as a subgroup of $\mathrm{GL}_2(\mathbb{R})$: for every $\gamma$ in that subgroup, $f \mid[k] \gamma = f$. Write $U_p$ for the operator [`ModularForm.heckeU k p`](def/ModularForm_HeckeOperator.html#L93), which sends $f$ to the finite sum $\sum_{j=0}^{p-1} f \mid[k] M_{p,j}$, where $M_{p,j} \in \mathrm{GL}_2(\mathbb{R})$ is the upper triangular matrix $\begin{pmatrix} 1 & j \\ 0 & p\end{pmatrix}$ for $p \neq 0$ and the identity for $p = 0$ (in which case the sum is empty in any case). The assertion is that for every $\gamma \in \mathrm{GL}_2(\mathbb{R})$ lying in the congruence subgroup $\Gamma_0(N/p)$, with $N/p$ the quotient in natural-number division, one has $(U_p f) \mid[k] \gamma = U_p f$. Thus the weight-$k$ invariance of $f$ under $\Gamma_0(N)$ upgrades to invariance of $U_p f$ under the larger group $\Gamma_0(N/p)$.
--
--   This is the level-lowering property of the Hecke operator $U_p$ at a prime whose square divides the level, in the form given by Atkin–Lehner and by Li, stated here at the level of arbitrary functions on $\mathbb{H}$ rather than of modular forms. It is used in the comparison of $q$-expansion function fields for $\Gamma_0(N)$ and $\Gamma_0(N/p)$ and in the construction of cusp forms expressed as powers of $U_p$ applied to a given form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0_div.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.heckeU_slash_eq_self_of_mem_Gamma0_div {N : ℕ} (k : ℤ) {p : ℕ} (hp2N : p ^ 2 ∣ N) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)),
      SlashAction.map k γ f = f)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hγ : γ ∈ (CongruenceSubgroup.Gamma0 (N / p) : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    SlashAction.map k γ (ModularForm.heckeU k p f) = ModularForm.heckeU k p f := by sorry
