-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_of_isCosetEigenfunction_of_norm_eq_one
-- name    : LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_of_isCosetEigenfunction_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/98b7f9e5-1c3e-5f71-9ed8-2d21e5d9b322
-- title:
--   Cyclicity of a unitary spherical Whittaker function on GL₃
-- statement:
--   Let $v$ be a nonzero prime ideal of the ring of integers of $\mathbb{Q}$, let $\psi_v$ be an additive character of the $v$-adic completion $\mathbb{Q}_v$ with values in $\mathbb{C}$, and let $\alpha_0,\alpha_1,\alpha_2$ be complex numbers with $\|\alpha_i\|=1$. Let $W:\mathrm{GL}_3(\mathbb{Q}_v)\to\mathbb{C}$ be a function subject to the following conditions. First, $W(gu)=W(g)$ for every $g$ and every $u$ in `localMaximalCompact3`, the subgroup of matrices all of whose entries, and all of whose inverse's entries, have valuation at most $1$. Second, $W$ is a coset eigenfunction for the generator $\mathrm{diag}(\varpi,1,1)$ with eigenvalue $q(\alpha_0+\alpha_1+\alpha_2)$ and for $\mathrm{diag}(\varpi,\varpi,1)$ with eigenvalue $q(\alpha_0\alpha_1+\alpha_0\alpha_2+\alpha_1\alpha_2)$, where $\varpi$ is the chosen uniformiser, $q$ is the absolute norm of $v$, and being a coset eigenfunction with eigenvalue $\lambda$ means that $\sum_i W(g\,r_i)=\lambda W(g)$ for every $g$ and every finite family $(r_i)$ of elements of the double coset of the generator whose images in $\mathrm{GL}_3(\mathbb{Q}_v)/\,$`localMaximalCompact3` are injective and exhaust the cosets met by that double coset. Third, $W(\mathrm{diag}(\varpi,\varpi,\varpi)\,g)=\alpha_0\alpha_1\alpha_2\,W(g)$ for all $g$. Fourth, $W(n(x,y,z)g)=\psi_v(x+y)W(g)$ for all $x,y,z\in\mathbb{Q}_v$ and all $g$, where $n(x,y,z)$ is the upper unipotent matrix with superdiagonal entries $x,y$ and corner entry $z$. Finally, the level of $\psi_v$, namely the supremum of the integers $n$ such that $\psi_v$ is trivial on all $x$ with $\mathrm{v}(x)\le \exp n$, is $0$, and $\psi_v$ is not the trivial character. The conclusion is that for every $F$ in the $\mathbb{C}$-span of the right translates $g\mapsto W(gh)$ of $W$, if $F\neq 0$ then $W$ itself lies in the $\mathbb{C}$-span of the right translates of $F$.
--
--   The assertion is the cyclicity, equivalently the irreducibility, of the space of right translates of a spherical Whittaker function on $\mathrm{GL}_3(\mathbb{Q}_v)$ whose Satake parameters $\alpha_0,\alpha_1,\alpha_2$ have modulus one: each nonzero vector of the cyclic subspace generates the whole of it. It is used at the local places in the construction of the cubic induction, being cited by [`LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_of_isInducedSphericalAt_of_isUnitaryChar`](thm.html#LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_of_isInducedSphericalAt_of_isUnitaryChar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_of_isCosetEigenfunction_of_norm_eq_one.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_of_isCosetEigenfunction_of_norm_eq_one
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (α : Fin 3 → ℂ) (hα : ∀ i, ‖α i‖ = 1) (W : LocalGL3 v → ℂ)
    (hU : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hT₁ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W
      (cNormQ v * (α 0 + α 1 + α 2)))
    (hT₂ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W
      (cNormQ v * (α 0 * α 1 + α 0 * α 2 + α 1 * α 2)))
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = α 0 * α 1 * α 2 * W g)
    (hψ : IsGL3PsiWhittakerFn ψv W) (hlev : LanglandsTunnell.TateLocal.addCharLevel ψv = 0) (hne : ψv ≠ 1) :
    ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F := by sorry
