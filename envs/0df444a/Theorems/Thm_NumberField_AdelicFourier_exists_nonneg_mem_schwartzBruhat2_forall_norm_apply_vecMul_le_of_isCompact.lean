-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_forall_norm_apply_vecMul_le_of_isCompact
-- name    : NumberField.AdelicFourier.exists_nonneg_mem_schwartzBruhat2_forall_norm_apply_vecMul_le_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/08c53171-d66e-5f95-8dcc-ccdf2d5ac811
-- title:
--   Domination of a Schwartz–Bruhat function and its compact translates
-- statement:
--   Let $F$ be a number field, with $\mathbb{A}_F$ its adele ring (the adeles of $F$ over the ring of integers $\mathcal{O}_F$), and consider functions on the space $\mathbb{A}_F^2$ of pairs of adeles indexed by `Fin 2`. Write $\mathcal{S}$ for the complex subspace `schwartzBruhat2 F` of $\mathbb{C}$-valued functions on $\mathbb{A}_F^2$, namely the $\mathbb{C}$-span of the pure tensors $x \mapsto g(x_\infty)\,h(x_f)$ in which $g$ is a Schwartz function on two copies of the mixed space of $F$ (the archimedean coordinates being transported along the ring equivalence of the infinite adele ring with the mixed space) and $h$ is a locally constant, compactly supported function of the two finite-adelic coordinates. Let $\Phi \in \mathcal{S}$, and let $K$ be a compact subset of $\mathrm{GL}_2(\mathbb{A}_F)$, the group of invertible $2 \times 2$ matrices over $\mathbb{A}_F$. The assertion is that there exists $\Psi \in \mathcal{S}$ such that: every value $\Psi(x)$ is real, equal to its own real part, and $\operatorname{Re}\Psi(x) \ge 0$; $\|\Phi(x)\| \le \operatorname{Re}\Psi(x)$ for all $x \in \mathbb{A}_F^2$; and for every $g \in K$ and every $x$, $\|\Phi(x g)\| \le \operatorname{Re}\Psi(x)$, where $x g$ is the row vector $x$ multiplied on the right by the matrix underlying $g$.
--
--   This is the standard domination lemma of Schwartz–Bruhat theory: a single non-negative Schwartz–Bruhat function majorises a given one together with all of its right translates by a compact set of matrices, which makes estimates for adelic theta sums locally uniform in the group variable. It is used in the bounds for the reflected pair of a Schwartz–Bruhat function underlying the analytic theory of the adelic zeta integrals on $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_forall_norm_apply_vecMul_le_of_isCompact.lean

import Definitions.Def_AutomorphicForm_GodementSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicFourier AutomorphicForm

theorem NumberField.AdelicFourier.exists_nonneg_mem_schwartzBruhat2_forall_norm_apply_vecMul_le_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ schwartzBruhat2 F)
    (K : Set (AdelicGL2 (𝓞 F) F)) (hK : IsCompact K) :
    ∃ Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ, Ψ ∈ schwartzBruhat2 F ∧
      (∀ x : Fin 2 → AdeleRing (𝓞 F) F, (((Ψ x).re : ℝ) : ℂ) = Ψ x ∧ 0 ≤ (Ψ x).re) ∧
      (∀ x : Fin 2 → AdeleRing (𝓞 F) F, ‖Φ x‖ ≤ (Ψ x).re) ∧
      ∀ g ∈ K, ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
        ‖Φ (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖ ≤ (Ψ x).re := by sorry
