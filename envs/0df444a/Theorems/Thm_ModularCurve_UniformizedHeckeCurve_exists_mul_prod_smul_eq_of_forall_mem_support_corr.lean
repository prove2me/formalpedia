-- Prove2me | Theorems.Thm_ModularCurve_UniformizedHeckeCurve_exists_mul_prod_smul_eq_of_forall_mem_support_corr
-- name    : ModularCurve.UniformizedHeckeCurve.exists_mul_prod_smul_eq_of_forall_mem_support_corr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/3be30a28-bf1f-5e1f-8ee8-0dd8cede30ca
-- title:
--   Hecke cycles of places produce fixed points in Γ
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ and let $F_c$ be a field equipped with a $\mathbb{C}$-algebra structure, and let $U$ be a uniformized Hecke curve for $\Gamma$ over $F_c$: thus $U$ provides a map $\mathrm{pt}$ from the upper half plane $\mathfrak{H}$ to the places of $F_c$ over $\mathbb{C}$ (a place being a proper valuation subring of $F_c$ containing the image of $\mathbb{C}$ and being a principal ideal ring), together with the further data of $U$, among which: $\mathrm{pt}\,\tau = \mathrm{pt}\,\tau'$ holds exactly when $\tau' = \gamma\cdot\tau$ for some $\gamma \in \Gamma$, and for each prime $\ell$ a finite multiset $U.\mathrm{heckePoints}\ \ell$ of elements of $\mathrm{GL}_2(\mathbb{R})$ and an additive endomorphism $U.\mathrm{corr}\ \ell$ of the group of divisors (finitely supported $\mathbb{Z}$-valued functions on places) satisfying $U.\mathrm{corr}\ \ell\,[\mathrm{pt}\,\tau] = \sum_{\delta}[\mathrm{pt}(\delta\cdot\tau)]$, the sum over that multiset. Let $e \in \mathbb{N}$, let $\ell_0,\dots,\ell_{e-1}$ be primes, let $P_0,\dots,P_e$ be places, and let $\tau_0 \in \mathfrak{H}$ satisfy $\mathrm{pt}\,\tau_0 = P_0$; assume $P_{j+1}$ lies in the support of $U.\mathrm{corr}\ \ell_j\,[P_j]$ for each $j$, and $P_e = P_0$. Then there exist $\delta_j \in U.\mathrm{heckePoints}\ \ell_j$ for $j < e$ and $\gamma \in \Gamma$ with $(\gamma\,\delta_{e-1}\cdots\delta_1\delta_0)\cdot\tau_0 = \tau_0$, the product being that of the reversal of $[\delta_0,\dots,\delta_{e-1}]$.
--
--   This is the bookkeeping step turning a closed cycle of places under Hecke correspondences into a fixed point: a composite of Hecke matrices, corrected by an element of $\Gamma$, stabilises the chosen point of the upper half plane. It is used in the Čerednik–Drinfel'd part of the argument, in the construction of a finite set of fake elliptic curves avoiding prescribed Hecke relations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_UniformizedHeckeCurve_exists_mul_prod_smul_eq_of_forall_mem_support_corr.lean

import Definitions.Def_ModularCurve_UniformizedHeckeCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Topology
open ModularCurve

theorem ModularCurve.UniformizedHeckeCurve.exists_mul_prod_smul_eq_of_forall_mem_support_corr
    {Γ : Subgroup (GL (Fin 2) ℝ)} {Fc : Type} [Field Fc] [Algebra ℂ Fc] (U : UniformizedHeckeCurve Γ Fc)
    (e : ℕ) (ℓ : Fin e → ℕ) (hℓ : ∀ j, (ℓ j).Prime) (P : Fin (e + 1) → AlgebraicCurve.Place ℂ Fc)
    (τ₀ : UpperHalfPlane) (h0 : U.pt τ₀ = P 0)
    (hstep : ∀ j : Fin e, P j.succ ∈ (U.corr (ℓ j) (hℓ j) (Finsupp.single (P j.castSucc) 1)).support)
    (hlast : P (Fin.last e) = P 0) :
    ∃ (δ : Fin e → GL (Fin 2) ℝ) (γ : GL (Fin 2) ℝ),
      (∀ j, δ j ∈ U.heckePoints (ℓ j) (hℓ j)) ∧ γ ∈ Γ ∧
      (γ * ((List.ofFn δ).reverse).prod) • τ₀ = τ₀ := by sorry
