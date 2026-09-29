-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_stable_submodule_inf_eq_bot_and_sub_mem_of_positive_skew_form
-- name    : LanglandsTunnell.CubicInduction.exists_stable_submodule_inf_eq_bot_and_sub_mem_of_positive_skew_form
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/b4774ac8-6a0e-5668-bfdc-ade8695556f7
-- title:
--   Invariant complement for a positive skew-symmetric form
-- statement:
--   Let $M$ and $N$ be $\mathbb{C}$-subspaces of the space of complex-valued functions on $\mathrm{GL}_3$ over the adele ring of $\mathbb{Q}$, with $N \le M$. Both are assumed stable under two operations: right translation $w \mapsto (g \mapsto w(gk))$ by any $k$ whose component at every height-one prime of $\mathbb{Z}$ is the identity and whose archimedean component $K$ satisfies $K^{\mathsf T}K = 1$; and the nine operators $\mathrm{archDeriv}\ i\ j$ ($i,j \in \mathrm{Fin}\ 3$), sending $w$ to $g \mapsto \frac{d}{ds}\,w\bigl(g\cdot \mathrm{archRealLift3}(1 + s E_{ij})\bigr)\big|_{s=0}$, where $\mathrm{archRealLift3}$ sends a real $3\times 3$ matrix to the corresponding adelic element when it is a unit and to $1$ otherwise. Let $B$ be a $\mathbb{C}$-valued form on functions satisfying, on $M$: Hermitian symmetry $B(w',w) = \overline{B(w,w')}$; linearity $B(zw_1+w_2,w') = zB(w_1,w')+B(w_2,w')$; positivity $\mathrm{Re}\,B(w,w) > 0$ for $w \neq 0$; skewness of each $\mathrm{archDeriv}\ i\ j$; and invariance under the translations above. Let $P$ be a $\mathbb{C}$-linear endomorphism of $M$ carrying elements of $M$ lying in $N$ into $N$, idempotent, self-adjoint for $B$, and with finite-dimensional range, and let $v \in M$ with $Pv = v$. Then there is a subspace $M' \le M$, stable under the same translations and the nine derivative operators, with $M' \cap N = 0$, and containing some $v'$ with $v - v' \in N$.
--
--   This is the statement that the kernel $N$ of an equivariant map out of a unitary module admits an invariant complement reaching a prescribed vector of finite type, in the concrete setting of spaces of functions on $\mathrm{GL}_3$ of the adeles of $\mathbb{Q}$ that are smooth for the orthogonal translations and the archimedean derivatives. It is used in [`LanglandsTunnell.CubicInduction.exists_separating_stable_submodule_of_equivariant_stable_submodule`](thm.html#LanglandsTunnell.CubicInduction.exists_separating_stable_submodule_of_equivariant_stable_submodule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_stable_submodule_inf_eq_bot_and_sub_mem_of_positive_skew_form.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_stable_submodule_inf_eq_bot_and_sub_mem_of_positive_skew_form
    (M N : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (hNM : N ≤ M)
    (hM4 : (∀ w ∈ M, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ M))
    (hM5 : (∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M))
    (hN4 : (∀ w ∈ N, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ N))
    (hN5 : (∀ w ∈ N, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ N))
    (B : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℂ)
    (hB : (∀ w ∈ M, ∀ w' ∈ M, B w' w = (starRingEnd ℂ) (B w w')) ∧
        (∀ (z : ℂ), ∀ w₁ ∈ M, ∀ w₂ ∈ M, ∀ w' ∈ M, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w') ∧
        (∀ w ∈ M, w ≠ 0 → 0 < (B w w).re) ∧
        (∀ w ∈ M, ∀ w' ∈ M, ∀ i j : Fin 3,
          B (WhittakerBlock.archDeriv i j w) w' = - B w (WhittakerBlock.archDeriv i j w')) ∧
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            ∀ w ∈ M, ∀ w' ∈ M, B (fun g => w (g * k)) (fun g => w' (g * k)) = B w w')
    (P : ↥M →ₗ[ℂ] ↥M)
    (hPN : ∀ w : ↥M, (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ N → ((P w : ↥M) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ N)
    (hPP : ∀ w : ↥M, P (P w) = P w)
    (hPB : ∀ w w' : ↥M, B (P w) w' = B w (P w'))
    (hPfin : FiniteDimensional ℂ ↥(LinearMap.range P))
    (v : ↥M) (hPv : P v = v) :
    ∃ M' : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), M' ≤ M ∧
      (∀ w ∈ M', ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ M') ∧
      (∀ w ∈ M', ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M') ∧
      M' ⊓ N = ⊥ ∧
      ∃ v' ∈ M', (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - v' ∈ N := by sorry
