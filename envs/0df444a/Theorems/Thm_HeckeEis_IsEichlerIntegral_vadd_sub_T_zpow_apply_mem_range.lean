-- Prove2me | Theorems.Thm_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range
-- name    : HeckeEis.IsEichlerIntegral.vadd_sub_T_zpow_apply_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/c06c9099-8cfb-5ca1-83ab-9dffa3cf0345
-- title:
--   Parabolic condition for Eichler integrals at ∞
-- statement:
--   Fix $n \in \mathbb{N}$ and a non-zero integer $h$, and let $\rho_n =$ [`HeckeEis.binaryFormRepSL ℂ n`](def/HeckeEis_BinaryFormRep.html#L61) be the representation of $\mathrm{SL}_2(\mathbb{Z})$ on the submodule $\mathrm{BinaryForm}\,\mathbb{C}\,n$ of degree-$n$ homogeneous elements of $\mathbb{C}[X_0,X_1]$ given by the linear substitution $X_j \mapsto \sum_i M_{ij} X_i$ attached to the integral matrix $M$ of the group element. Let $g : \mathfrak{H} \to \mathbb{C}$ and $G : \mathfrak{H} \to \mathrm{BinaryForm}\,\mathbb{C}\,n$ be functions on the upper half plane such that: (i) [`HeckeEis.IsEichlerIntegral n g G`](def/HeckeEis_EichlerIntegral.html#L105) holds, i.e. for every multidegree $d$ and every $\tau \in \mathfrak{H}$ the function $z \mapsto \mathrm{coeff}_d\,G(z)$ (with $G$ extended to $\mathbb{C}$ through `UpperHalfPlane.ofComplex`) has derivative $g(\tau)\,\mathrm{coeff}_d\bigl((\tau X_0 + X_1)^n\bigr)$ at $\tau$; (ii) $g \circ$ `ofComplex` is periodic with period $h$ (viewed as a complex number); (iii) $g$ is holomorphic, in the sense of being differentiable for the complex manifold structures on $\mathfrak{H}$ and $\mathbb{C}$; and (iv) $g$ is zero at $i\infty$. Then for every $\tau \in \mathfrak{H}$,
--   $$G(h + \tau) - \rho_n(T^h)\,G(\tau) \in \operatorname{range}\bigl(\rho_n(T^h) - 1\bigr),$$
--   where $T$ is the standard parabolic generator $\begin{pmatrix}1&1\\0&1\end{pmatrix}$ and $h + \tau$ denotes the translation action of the real number $h$ on $\mathfrak{H}$.
--
--   This is the parabolic (cusp at $\infty$) condition satisfied by the Eichler–Shimura cocycle attached to an Eichler integral of a cusp form, stated here for an arbitrary non-zero translation length $h$ and without reference to any congruence subgroup. It feeds into [`HeckeEis.isParabolicCocycle_cocycle_of_isEichlerIntegral`](thm.html#HeckeEis.isParabolicCocycle_cocycle_of_isEichlerIntegral), where the cocycle built from $G$ is shown to be parabolic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold MatrixGroups

theorem HeckeEis.IsEichlerIntegral.vadd_sub_T_zpow_apply_mem_range {n : ℕ} {h : ℤ} (hh : h ≠ 0)
    {g : UpperHalfPlane → ℂ} {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G)
    (hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) ((h : ℝ) : ℂ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hzero : UpperHalfPlane.IsZeroAtImInfty g) (τ : UpperHalfPlane) :
    G ((h : ℝ) +ᵥ τ) - HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ h) (G τ)
      ∈ LinearMap.range (HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ h) - 1) := by sorry
