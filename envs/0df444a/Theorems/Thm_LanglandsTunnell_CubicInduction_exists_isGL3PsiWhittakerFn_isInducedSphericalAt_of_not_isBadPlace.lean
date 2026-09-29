-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace
-- name    : LanglandsTunnell.CubicInduction.exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/c7287e86-dc28-5743-8457-a56ec26be5a8
-- title:
--   Good-place spherical Whittaker function for cubic induction
-- statement:
--   Let $K$ be a number field of degree $3$ over $\mathbb{Q}$, with $\mathcal{O}_K$ an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, let $\mu\colon (\mathbb{A}_K)^{\times}\to\mathbb{C}^{\times}$ be a character of the idele group of $K$, and let $v$ be a height one prime of $\mathcal{O}_{\mathbb{Q}}$ which is not a bad place for $(K,\mu)$, i.e. neither `IsRamifiedIn K v` nor `IsTwistRamifiedAbove K μ v` holds. Let $\psi$ be an additive character of the adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$, and write $\psi_v=$ `psiLoc ψ v` for its component at $v$, the composite of $\psi$ with the inclusion of $\mathbb{Q}_v$ as the single coordinate at $v$. Assume $\psi_v(x)=1$ whenever $\mathrm{v}(x)\le 1$, and that $\psi_v(\varpi_v^{-1}x)\neq 1$ for some $x$ with $\mathrm{v}(x)\le 1$, where $\varpi_v$ is the chosen uniformiser of $\mathbb{Q}_v$. Then there exists $W\colon \mathrm{GL}_3(\mathbb{Q}_v)\to\mathbb{C}$ with the following four properties. First, $W$ is a $\psi_v$-Whittaker function for the upper unipotent: $W(u(x,y,z)g)=\psi_v(x+y)W(g)$ for all $x,y,z\in\mathbb{Q}_v$ and all $g$, where $u(x,y,z)$ is the unipotent matrix with rows $(1,x,z),(0,1,y),(0,0,1)$. Secondly, $W$ is spherical for the induced coefficients $c=$ `inducedCoeff K μ` (given by $c(\mathfrak{P})=\mu$ of the uniformiser idele at $\mathfrak{P}$ when $\mu$ is unramified at $\mathfrak{P}$, and $0$ otherwise) at the maximal compact subgroup $U$ of matrices all of whose entries, and all of whose inverse's entries, have valuation $\le 1$: $W$ is right $U$-invariant; for every finite family of representatives forming a Hecke coset system for $U$ and $\mathrm{diag}(\varpi_v,1,1)$, resp. for $U$ and $\mathrm{diag}(\varpi_v,\varpi_v,1)$, the associated coset sum of $W$ equals $N(v)\,e_1\cdot W$, resp. $N(v)\,e_2\cdot W$, where $N(v)$ is the absolute norm of $v$ viewed in $\mathbb{C}$ and $e_1,e_2$ are `inducedE1 ℚ c v`, `inducedE2 ℚ c v`; and $W(\mathrm{diag}(\varpi_v,\varpi_v,\varpi_v)g)=e_3W(g)$ with $e_3=$ `inducedE3 ℚ c v`. Thirdly, $W(1)=1$. Fourthly, $W$ has the prescribed spherical torus values: $W(\mathrm{iotaTorusLocal}\,v\,n)=N(v)^{-n}S(n)$ for all $n\in\mathbb{N}$, and $W(\mathrm{twoRowPointLocal}\,v\,k_1\,(k_2+1))=N(v)^{-k_1}\bigl(S(k_1)S(k_2+1)-S(k_1+1)S(k_2)\bigr)$ whenever $k_2+1\le k_1$, where $S(m)=$ `sphericalTorusValue e₁ e₂ e₃ m`.
--
--   This is the local package at a place of good reduction in the construction of the automorphic induction from a cubic field: it produces the normalised spherical Whittaker function on $\mathrm{GL}_3(\mathbb{Q}_v)$ whose Hecke eigenvalues and torus values are those dictated by the induced Satake data of $\mu$ at $v$. It feeds into [`LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad`](thm.html#LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad), where the local data at all places are assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsBadPlace K μ v)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLoc ψ v x = 1)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLoc ψ v ((varpi v)⁻¹ * x) ≠ 1) :
    ∃ W : LocalGL3 v → ℂ,
      IsGL3PsiWhittakerFn (psiLoc ψ v) W ∧
      IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      W 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v W := by sorry
