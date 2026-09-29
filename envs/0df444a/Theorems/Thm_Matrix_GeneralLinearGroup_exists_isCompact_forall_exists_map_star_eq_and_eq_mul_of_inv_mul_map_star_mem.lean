-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_exists_isCompact_forall_exists_map_star_eq_and_eq_mul_of_inv_mul_map_star_mem
-- name    : Matrix.GeneralLinearGroup.exists_isCompact_forall_exists_map_star_eq_and_eq_mul_of_inv_mul_map_star_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/2f49b51e-7062-5ef4-8b60-4a1616dc6bec
-- title:
--   Uniform Hilbert 90 for GL₂(ℂ)/GL₂(ℝ)
-- statement:
--   Let $B$ be a set of complex $2\times 2$ matrices which is compact in the usual topology on $\mathrm{Matrix}(\mathrm{Fin}\,2,\mathrm{Fin}\,2,\mathbb{C})$. The assertion is that there is a set $K\subseteq \mathrm{GL}_2(\mathbb{C})$, compact in the topology of the unit group, with the following property: for every $x\in \mathrm{GL}_2(\mathbb{C})$ such that the matrix product of $x^{-1}$ with the entrywise complex conjugate $\overline{x}$ of $x$ (conjugation applied by `starRingEnd ℂ` through `Matrix.map`, so entrywise and with no transposition) lies in $B$, there exist $m,k\in\mathrm{GL}_2(\mathbb{C})$ with $\overline{m}=m$, i.e. $m$ has real entries, with $k\in K$, and with $x=m\,k$. Thus the compact set $K$ depends only on $B$ and not on $x$: the factorisation $x=mk$ with $m\in\mathrm{GL}_2(\mathbb{R})$ can be chosen with the $\mathrm{GL}_2(\mathbb{R})$-free part $k$ confined to one compact set, uniformly over all $x$ whose associated cocycle value $x^{-1}\overline{x}$ is constrained to $B$.
--
--   This is a quantitative, compactness-uniform form of Hilbert's Theorem 90 for $\mathrm{GL}_2$ over the extension $\mathbb{C}/\mathbb{R}$ (Speiser's form: every cocycle $x^{-1}\overline{x}$ is a coboundary, here with control on the cocycle-splitting factor). It is used in the proof of [`AutomorphicForm.exists_nhds_one_forall_isCompact_exists_eq_toTensorGL_mul_of_conjAe_twistedConj_mem`](thm.html#AutomorphicForm.exists_nhds_one_forall_isCompact_exists_eq_toTensorGL_mul_of_conjAe_twistedConj_mem), where properness/compactness statements about automorphic quotients require such a uniform descent from $\mathrm{GL}_2(\mathbb{C})$ to $\mathrm{GL}_2(\mathbb{R})$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_GeneralLinearGroup_exists_isCompact_forall_exists_map_star_eq_and_eq_mul_of_inv_mul_map_star_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.GeneralLinearGroup.exists_isCompact_forall_exists_map_star_eq_and_eq_mul_of_inv_mul_map_star_mem
    (B : Set (Matrix (Fin 2) (Fin 2) ℂ)) (hB : IsCompact B) :
    ∃ K : Set (GL (Fin 2) ℂ), IsCompact K ∧
      ∀ x : GL (Fin 2) ℂ,
        ((x⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * ((x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) ∈ B →
        ∃ m k : GL (Fin 2) ℂ,
          ((m : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) = m ∧ k ∈ K ∧ x = m * k := by sorry
