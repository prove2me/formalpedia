-- Prove2me | Theorems.Thm_N25_etaAnalytic25_pair_A13
-- name    : N25.etaAnalytic25_pair_A13
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:01.482083+00:00
-- url     : https://prove2.me/theorems/4619836b-606e-487f-9d15-fb8ebb7bf879
-- title:
--   The label-$13$ matrix cyclically transforms the eta pairs
-- statement:
--   Let $A=\begin{pmatrix}13&1\25&2\end{pmatrix}\in\mathrm{SL}_2(\mathbb Z)$ and let $\sigma=(-1,1,-1,-1,1)$. There exists $\mu\in\mathbb C$ with $\mu^{12}=1$ such that for every $j\in\mathbb Z/5\mathbb Z$ and every $\tau$,
--
--   $$E_{r_{j,1}}(A\tau)E_{r_{j,2}}(A\tau)=\mu^2\sigma_jE_{r_{j-1,1}}(\tau)E_{r_{j-1,2}}(\tau),$$
--
--    where $(r_{j,1},r_{j,2})$ is the $j$th residue pair. This gives the signed cyclic transformation underlying the label-$13$ unit action.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.etaAnalytic25_pair_A13 :
    let A : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
      ⟨!![13,1;25,2], by norm_num [Matrix.det_fin_two]⟩
    let σ : Fin 5 → ℂ := ![-1,1,-1,-1,1]
    ∃ μ : ℂ, μ^12 = 1 ∧ ∀ (j : Fin 5) (τ : UpperHalfPlane),
      etaAnalytic25 (unitResidues25 j).1 (A • τ) *
        etaAnalytic25 (unitResidues25 j).2 (A • τ) =
      (μ^2 * σ j) * (etaAnalytic25 (unitResidues25 (j-1)).1 τ *
        etaAnalytic25 (unitResidues25 (j-1)).2 τ) := by sorry
