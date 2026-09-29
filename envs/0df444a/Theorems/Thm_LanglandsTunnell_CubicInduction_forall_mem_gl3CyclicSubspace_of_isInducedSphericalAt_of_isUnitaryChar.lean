-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_of_isInducedSphericalAt_of_isUnitaryChar
-- name    : LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_of_isInducedSphericalAt_of_isUnitaryChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/ec2d4c03-6b14-56df-b979-732dd3798fab
-- title:
--   Cyclicity of induced spherical Whittaker functions on GL₃(ℚᵥ)
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$, whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, and let $\mu$ be a homomorphism from the ideles of $K$ to $\mathbb{C}^{\times}$ with $|\mu(x)|=1$ for every idele $x$. Let $v$ be a nonzero prime of $\mathcal{O}_{\mathbb{Q}}$ and let $W\colon \mathrm{GL}_3(\mathbb{Q}_v)\to\mathbb{C}$, where $\mathbb{Q}_v$ denotes the completion at $v$. Write $c=$ `inducedCoeff K μ` for the function sending a prime $\mathfrak{P}$ of $\mathcal{O}_K$ to $\mu$ of the uniformiser idele at $\mathfrak{P}$ when $\mu$ is unramified at $\mathfrak{P}$, and to $0$ otherwise, and let $U=$ `localMaximalCompact3` be the subgroup of those $k\in\mathrm{GL}_3(\mathbb{Q}_v)$ all of whose entries and all of whose entries of $k^{-1}$ have valuation $\le 1$. The hypothesis `IsInducedSphericalAt` asserts four things: $W(gu)=W(g)$ for all $g$ and all $u\in U$; for the diagonal element $\mathrm{diag}(\varpi_v,1,1)$ and for $\mathrm{diag}(\varpi_v,\varpi_v,1)$, every finite family of representatives forming a Hecke coset system for $U$ and that element has coset sum equal to $N(v)\cdot$`inducedE1 ℚ c v` times $W$, respectively $N(v)\cdot$`inducedE2 ℚ c v` times $W$, where $N(v)$ is the absolute norm of $v$; and $W(\mathrm{diag}(\varpi_v,\varpi_v,\varpi_v)\,g)=$ `inducedE3 ℚ c v` $\cdot W(g)$ for all $g$. Let $\psi_v$ be an additive character of $\mathbb{Q}_v$ with values in $\mathbb{C}$ such that $W(n(x,y,z)g)=\psi_v(x+y)W(g)$ for all $x,y,z\in\mathbb{Q}_v$ and all $g$, where $n(x,y,z)$ is the upper unipotent matrix with entries $x,z$ in the first row and $y$ in position $(2,3)$; assume moreover that the level of $\psi_v$, namely the supremum of the integers $n$ with $\psi_v(x)=1$ whenever $v(x)\le \exp(n)$, is $0$, and that $\psi_v$ is not the trivial character. Then for every $F$ in the $\mathbb{C}$-span of the right translates of $W$ with $F\neq 0$, the function $W$ lies in the $\mathbb{C}$-span of the right translates of $F$.
--
--   This is the cyclicity (or regeneration) property of the local Whittaker function attached at a finite place of $\mathbb{Q}$ to the cubic induction of a unitary idele class character, in the form needed for the converse-theorem input to Langlands–Tunnell: any nonzero element of the span of the right translates of $W$ generates $W$ back. It is deduced from the corresponding statement for Whittaker eigenfunctions whose three Satake parameters have modulus one, and is used in the construction of the local zeta integrals and their functional equations, and in the Rankin–Selberg comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_of_isInducedSphericalAt_of_isUnitaryChar.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.Converse

theorem LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_of_isInducedSphericalAt_of_isUnitaryChar
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 K) K μ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ)
    (hsph : IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψ : IsGL3PsiWhittakerFn ψv W)
    (hlev : LanglandsTunnell.TateLocal.addCharLevel ψv = 0) (hne : ψv ≠ 1) :
    ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F := by sorry
