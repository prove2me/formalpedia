-- Prove2me | Theorems.Thm_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1
-- name    : ModularForm.heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/b1622c8a-b275-58e0-9bd9-04b73e21d528
-- title:
--   Tₚ with diamond correction preserves Γ₁(N)-invariance
-- statement:
--   Fix $N \in \mathbb{N}$, an integer weight $k$, and a prime $p$ with $p \nmid N$. Let $f : \mathbb{H} \to \mathbb{C}$ be a function invariant under the weight-$k$ slash action of every element of the image of $\Gamma_1(N) \le \mathrm{SL}_2(\mathbb{Z})$ in $\mathrm{GL}_2(\mathbb{R})$, i.e. $f \mid_k \gamma = f$ for all such $\gamma$. Let $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(N)$ and have lower-right entry congruent to $p$ modulo $N$, and let $\gamma$ be any element of $\mathrm{GL}_2(\mathbb{R})$ coming from $\Gamma_1(N)$. The assertion is that the function $$\sum_{j=0}^{p-1} f \Big|_k \begin{pmatrix} 1 & j \\ 0 & p \end{pmatrix} \; + \; \bigl(f \mid_k \sigma\bigr) \Big|_k \begin{pmatrix} p & 0 \\ 0 & 1 \end{pmatrix}$$ is fixed by $\mid_k \gamma$. Here the first summand is `heckeU k p f`, the sum over $j \in \{0,\dots,p-1\}$ of $f$ slashed by `heckeMatrix p j`, which for $p \neq 0$ is the upper-triangular matrix with rows $(1, j)$ and $(0, p)$, while `heckeDiagMatrix p` is, for $p \neq 0$, the matrix with rows $(p, 0)$ and $(0, 1)$; $\sigma$ acts through its image $\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{GL}_2(\mathbb{R})$ and $\mid_k$ is Mathlib's weight-$k$ slash action of $\mathrm{GL}_2(\mathbb{R})$.
--
--   This is the invariance half of the statement that the classical Hecke operator $T_p$, for $p \nmid N$ realised by the $p+1$ coset representatives $\begin{pmatrix} 1 & j \\ 0 & p \end{pmatrix}$ and $\sigma\begin{pmatrix} p & 0 \\ 0 & 1 \end{pmatrix}$ with $\sigma$ a lift of the diamond operator $\langle p \rangle$, maps weight-$k$ forms on $\Gamma_1(N)$ to weight-$k$ forms on $\Gamma_1(N)$; no holomorphy or growth condition is imposed on $f$, only $\Gamma_1(N)$-invariance. It feeds the construction of nebentypus characters for Hecke eigenforms, being used by [`CuspForm.slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen`](thm.html#CuspForm.slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen) and [`CuspForm.exists_hasNebentypus_of_qCoeff_hecke_eigen`](thm.html#CuspForm.exists_hasNebentypus_of_qCoeff_hecke_eigen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup ModularForm
open scoped ModularForm UpperHalfPlane MatrixGroups

theorem ModularForm.heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1
    {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (hσp : ((σ 1 1 : ℤ) : ZMod N) = p)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    (heckeU k p f + (f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ)) ∣[k] heckeDiagMatrix p) ∣[k] γ
      = heckeU k p f + (f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ)) ∣[k] heckeDiagMatrix p := by sorry
