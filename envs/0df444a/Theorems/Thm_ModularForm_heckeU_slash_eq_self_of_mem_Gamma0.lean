-- Prove2me | Theorems.Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0
-- name    : ModularForm.heckeU_slash_eq_self_of_mem_Gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/9f17ad58-ad6c-5a85-ac1d-ca32b4f24fd3
-- title:
--   Uₚ preserves weight-k invariance under Γ₀(N)
-- statement:
--   Let $N$ be a natural number, $k$ an integer, and $p$ a natural number dividing $N$. Let $f : \mathbb{H} \to \mathbb{C}$ be a function on the upper half-plane which is invariant under the weight-$k$ slash action of $\Gamma_0(N)$, in the sense that $f \mid_k \gamma = f$ for every $\gamma$ in the image of the congruence subgroup $\Gamma_0(N)$ inside $\mathrm{GL}_2(\mathbb{R})$. Let $\gamma$ be an element of $\mathrm{GL}_2(\mathbb{R})$ lying in that subgroup. The conclusion is that the function
--   $$\mathrm{heckeU}\,k\,p\,f \;=\; \sum_{j=0}^{p-1} f \mid_k M_{p,j}, \qquad M_{p,j} \;=\; \begin{pmatrix} 1 & j \\ 0 & p \end{pmatrix} \in \mathrm{GL}_2(\mathbb{R}) \ \ (M_{0,j} = 1),$$
--   satisfies $(\mathrm{heckeU}\,k\,p\,f) \mid_k \gamma = \mathrm{heckeU}\,k\,p\,f$; that is, the finite sum of weight-$k$ slashes of $f$ by the matrices $\begin{pmatrix} 1 & j \\ 0 & p \end{pmatrix}$, $0 \le j < p$, is again invariant under the weight-$k$ action of $\Gamma_0(N)$. No primality of $p$ is assumed, and $f$ is an arbitrary function, subject only to the invariance hypothesis: no holomorphy, growth or cusp condition enters.
--
--   This is the level-preservation half of the classical statement that the Atkin–Lehner operator $U_p$, for $p$ dividing the level $N$, acts on weight-$k$ modular forms for $\Gamma_0(N)$, isolated here at the level of bare functions invariant under the slash action. It is used by [`CuspForm.exists_coe_eq_heckeU`](thm.html#CuspForm.exists_coe_eq_heckeU), which produces a cusp form whose underlying function is $U_p f$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.heckeU_slash_eq_self_of_mem_Gamma0 {N : ℕ} (k : ℤ) {p : ℕ} (hpN : p ∣ N) {f : UpperHalfPlane → ℂ} (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map k γ f = f) (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) : SlashAction.map k γ (ModularForm.heckeU k p f) = ModularForm.heckeU k p f := by sorry
