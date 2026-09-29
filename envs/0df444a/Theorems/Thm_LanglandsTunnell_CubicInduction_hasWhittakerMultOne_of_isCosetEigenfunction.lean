-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_hasWhittakerMultOne_of_isCosetEigenfunction
-- name    : LanglandsTunnell.CubicInduction.hasWhittakerMultOne_of_isCosetEigenfunction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/ae482530-d581-51a7-ba15-4119be06783f
-- title:
--   Whittaker multiplicity one for a normalised spherical Whittaker function
-- statement:
--   Let $v$ be a nonzero prime of $\mathcal{O}_{\mathbb{Q}}$, let $\psi_v$ be an additive character of the completion $\mathbb{Q}_v$ with values in $\mathbb{C}$, let $e_1,e_2,e_3$ be complex numbers and let $W \colon \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ be a function. Assume: (hU) $W(gk)=W(g)$ for all $g$ and all $k$ in the subgroup `localMaximalCompact3` of those $k$ for which every entry of $k$ and of $k^{-1}$ has valuation $\le 1$; (hT₁) for every finite index type and every family of representatives satisfying `IsHeckeCosetSystem` for that subgroup and the element $\mathrm{diag}(\varpi,1,1)$, the sum of the translates $W(g\,\cdot)$ over the representatives equals $N(v)e_1\,W(g)$ for all $g$, where $\varpi$ is the chosen uniformiser and $N(v)$ the absolute norm of $v$, viewed in $\mathbb{C}$; (hT₂) the same with $\mathrm{diag}(\varpi,\varpi,1)$ and eigenvalue $N(v)e_2$; (hZ) $W(\mathrm{diag}(\varpi,\varpi,\varpi)\,g)=e_3W(g)$ for all $g$; (hψ) $W(n(x,y,z)g)=\psi_v(x+y)W(g)$ for all $x,y,z$ and $g$, where $n(x,y,z)$ is the upper triangular unipotent matrix with entries $x,y$ above the diagonal and $z$ in the corner; (hlev) the level of $\psi_v$, the supremum of the set of integers $n$ such that $\psi_v$ is trivial on $\{x : \mathrm{v}(x) \le \exp(n)\}$, is $0$; (hne) $\psi_v$ is not the trivial character; and (hW1) $W(1)=1$. The conclusion is `HasWhittakerMultOne ψv W`: the $\mathbb{C}$-rank of the space `gl3WhittakerFunctionalSpace` of $\psi_v$-Whittaker functionals attached to the right-translation representation `gl3CyclicRep W` of $\mathrm{GL}_3(\mathbb{Q}_v)$ on the span of the right translates of $W$ is at most $1$.
--
--   This is local multiplicity one, or uniqueness of Whittaker functionals, for the representation generated under right translation by a normalised spherical Whittaker function on $\mathrm{GL}_3$ over a non-archimedean local field with prescribed Hecke eigenvalues $N(v)e_1$, $N(v)e_2$ and central law $e_3$; the hypotheses are those of the class-one Whittaker function of an unramified principal series. It supplies the multiplicity-one part of the local data at the unramified places in the construction of the cubic induction package, and is cited by [`LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad`](thm.html#LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_hasWhittakerMultOne_of_isCosetEigenfunction.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.hasWhittakerMultOne_of_isCosetEigenfunction
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (e₁ e₂ e₃ : ℂ) (W : LocalGL3 v → ℂ)
    (hU : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hT₁ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁))
    (hT₂ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂))
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn ψv W) (hlev : LanglandsTunnell.TateLocal.addCharLevel ψv = 0) (hne : ψv ≠ 1)
    (hW1 : W 1 = 1) :
    HasWhittakerMultOne ψv W := by sorry
