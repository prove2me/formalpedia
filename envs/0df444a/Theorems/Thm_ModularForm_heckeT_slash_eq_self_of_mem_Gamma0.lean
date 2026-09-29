-- Prove2me | Theorems.Thm_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0
-- name    : ModularForm.heckeT_slash_eq_self_of_mem_Gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/2107b482-b48e-53c7-b123-455181e52920
-- title:
--   Tₚ preserves Γ₀(N)-invariance for p ∤ N
-- statement:
--   Let $N$ be a natural number, $k$ an integer and $p$ a prime with $p \nmid N$, and let $f : \mathbb{H} \to \mathbb{C}$ be an arbitrary function (no holomorphy or growth condition is imposed). Assume that $f$ is invariant under the weight-$k$ slash action of every element of $\Gamma_0(N)$, viewed through the coercion of `CongruenceSubgroup.Gamma0 N` into a subgroup of $\mathrm{GL}_2(\mathbb{R})$: $f \mid_k \gamma = f$ for all such $\gamma$. Then the function $$\mathrm{heckeT}\,k\,p\,f \;=\; \sum_{j=0}^{p-1} f \mid_k \mathtt{heckeMatrix}\,p\,j \;+\; f \mid_k \mathtt{heckeDiagMatrix}\,p,$$ where the last matrix is the identity when $p = 0$ and otherwise the upper-triangular element `upperTriangularGL p 0 1` of $\mathrm{GL}_2(\mathbb{R})$ with entries $p$, $0$, $1$, enjoys the same invariance: for every $\gamma \in \mathrm{GL}_2(\mathbb{R})$ lying in (the image of) $\Gamma_0(N)$ one has $(\mathrm{heckeT}\,k\,p\,f) \mid_k \gamma = \mathrm{heckeT}\,k\,p\,f$. The coset representatives $\mathtt{heckeMatrix}\,p\,j$, $0 \le j < p$, are the remaining terms of the Hecke sum.
--
--   This is the automorphy, or level-preservation, half of the assertion that the Hecke operator $T_p$ at a prime $p$ not dividing the level acts on modular forms for $\Gamma_0(N)$: the invariance under the weight-$k$ action of $\Gamma_0(N)$ is preserved, while holomorphy and the conditions at the cusps are treated separately. It is used by [`CuspForm.exists_coe_eq_heckeT`](thm.html#CuspForm.exists_coe_eq_heckeT), which realises $T_p$ as an operator on cusp forms of level $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.heckeT_slash_eq_self_of_mem_Gamma0 {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) {f : UpperHalfPlane → ℂ} (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map k γ f = f) (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) : SlashAction.map k γ (ModularForm.heckeT k p f) = ModularForm.heckeT k p f := by sorry
