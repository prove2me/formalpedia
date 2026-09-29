-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_hasCompactSupport_of_isSmoothingKernel
-- name    : LanglandsTunnell.CubicInduction.SlabL2.continuous_and_hasCompactSupport_of_isSmoothingKernel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/03bebb10-6026-5ee6-8e73-b3d2e13189ca
-- title:
--   Smoothing kernels on GL₃(A_ℚ) are continuous with compact support
-- statement:
--   Let $\varphi$ be a complex-valued function on `AdelicGL 3 (𝓞 ℚ) ℚ`, the general linear group of degree $3$ over the adele ring of $\mathbb{Q}$, and assume `IsSmoothingKernel φ`, that is: there exist a function $\alpha$ on $3\times 3$ real matrices (as functions $\mathrm{Fin}\,3 \to \mathrm{Fin}\,3 \to \mathbb{R}$) and a family of subgroups $K'_p \le \mathrm{GL}_3(\mathbb{Q}_p)$, one for each height-one prime $p$ of $\mathcal{O}_\mathbb{Q}$, with $\mathbb{Q}_p$ the $p$-adic completion, such that (i) $\alpha$ is $C^\infty$ on $\mathbb{R}^{3\times 3}$, has compact support, and its topological support is contained in the set of matrices of nonzero determinant; (ii) each $K'_p$ is open and compact as a subset of $\mathrm{GL}_3(\mathbb{Q}_p)$; (iii) for all but finitely many $p$, $K'_p$ equals `localMaximalCompact3`, the subgroup of those $k$ all of whose entries and all of whose entries of $k^{-1}$ have valuation $\le 1$; and (iv) for every $g$ one has $\varphi(g) = \alpha(\mathrm{archEntries}\,g)$ times the value at $g$ of the indicator function (with value $1 \in \mathbb{C}$) of the set of $x$ whose component at $p$ lies in $K'_p$ for every $p$, where $\mathrm{archEntries}\,g$ records the real coordinates of the archimedean components of the entries of $g$. Then $\varphi$ is continuous and has compact support.
--
--   This is the elementary regularity statement for the adelic test functions used as smoothing kernels: such a $\varphi$ lies in $C_c(\mathrm{GL}_3(\mathbb{A}_\mathbb{Q}))$, continuity and compactness of support coming from the restricted product topology, in which the level set $\{g : g_p \in K'_p \ \forall p\}$ is open and compact. It is invoked wherever smoothing operators are analysed on the cuspidal slab space, in particular in the treatment of their regularity and growth properties, their finiteness and archimedean differentiability properties, and the Casimir relations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_hasCompactSupport_of_isSmoothingKernel.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2

theorem LanglandsTunnell.CubicInduction.SlabL2.continuous_and_hasCompactSupport_of_isSmoothingKernel
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ) :
    Continuous φ ∧ HasCompactSupport φ := by sorry
