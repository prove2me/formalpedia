-- Prove2me | Theorems.Thm_ModularCurve_mazurPrinciple_of_ne_one_of_toricDichotomy
-- name    : ModularCurve.mazurPrinciple_of_ne_one_of_toricDichotomy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/fbbd0ceb-2425-57f2-b9c4-9332dce547d0
-- title:
--   Mazur's principle from the toric dichotomy when qnot≡ 1
-- statement:
--   Let $G$ be a group with a subgroup $I$, let $\mathbb{T}=\mathrm{MvPolynomial}\ \mathbb{P}\ \mathbb{Z}$ be the polynomial algebra [`ModularCurve.HeckeAlg`](def/HeckeGalois_EichlerShimura.html#L14) on indeterminates $T_\ell$ indexed by the primes, let $J$ be a $\mathbb{T}$-module carrying a distributive $G$-action, let $J_0$ be a $\mathbb{T}$-module, let $V$ be a vector space over a field $k$ with a distributive $G$-action commuting with the scalars, let $S$ be a finite set of primes, $\mathcal{T}\subseteq J$ a $\mathbb{T}$-submodule, $q$ a natural number and $\varphi\in G$. Assume: $\varphi\cdot\varphi\cdot x=q^2\cdot x$ for all $x\in\mathcal{T}$; the dichotomy `IsToricDichotomyQGuarded`, i.e. for every maximal ideal $\mathfrak{n}\subseteq\mathbb{T}$ that is not eventually Eisenstein (no finite set of primes off which $T_\ell-(\ell+1)\in\mathfrak{n}$) and for which $q$ is a unit in $\mathbb{T}/\mathfrak{n}$, every element of $J$ annihilated by $\mathfrak{n}$ and fixed by $I$ either lies in $\mathcal{T}$ or forces the conclusion below at $\mathfrak{n}$. Let $\mathfrak{m}$ be a maximal ideal of $\mathbb{T}$ that is not eventually Eisenstein and with $q$ a unit in $\mathbb{T}/\mathfrak{m}$. Let $\iota\colon V\to J$ be an injective additive $G$-equivariant map whose image is annihilated by $\mathfrak{m}$, with $\dim_k V=2$ and $\det(\varphi|_V)=q$ in $k$, with $I$ acting trivially on $V$, and such that if $\iota(V)\subseteq\mathcal{T}$ then $\varphi$ acts on $V$ by some scalar $\lambda\in k$. Assume $q\neq 0$ and $q\neq 1$ in $k$. Then `HasLowerLevelTorsion S 𝔪 J₀` holds: there is a nonzero $y\in J_0$ with $n\cdot y=0$ for every natural number $n$ lying in $\mathfrak{m}$ and $(T_\ell-b)\cdot y=0$ for every prime $\ell\notin S$ and every integer $b$ with $T_\ell-b\in\mathfrak{m}$.
--
--   This is the abstract core of Mazur's principle: at a non-Eisenstein maximal ideal of the Hecke algebra where $q$ is invertible and $q\not\equiv 1$, the two-dimensional $\mathfrak{m}$-torsion module with unramified $I$-action and determinant $q$ produces Hecke torsion at the lower level. It feeds the residual modularity step [`ModularCurve.isResiduallyModularOfLevel_div_of_mazurFamilies`](thm.html#ModularCurve.isResiduallyModularOfLevel_div_of_mazurFamilies), where level lowering at $q$ is carried out.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mazurPrinciple_of_ne_one_of_toricDichotomy.lean

import Mathlib
import Definitions.Def_ModularCurve_ToricDichotomyData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.mazurPrinciple_of_ne_one_of_toricDichotomy
    {G : Type*} [Group G] {I : Subgroup G}
    {J : Type*} [AddCommGroup J] [Module ModularCurve.HeckeAlg J] [DistribMulAction G J]
    {J₀ : Type*} [AddCommGroup J₀] [Module ModularCurve.HeckeAlg J₀]
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [DistribMulAction G V] [SMulCommClass G k V]
    {S : Finset Nat.Primes} {𝒯 : Submodule ModularCurve.HeckeAlg J}
    {q : ℕ} {φ : G}
    (hfrob : ModularCurve.ToricFrobeniusSq q φ 𝒯)
    (hdich : ModularCurve.IsToricDichotomyQGuarded q S I 𝒯 J₀)
    {𝔪 : Ideal ModularCurve.HeckeAlg} (hmax : 𝔪.IsMaximal)
    (heis : ¬ ModularCurve.IsEventuallyEisenstein 𝔪)
    (hqu : IsUnit ((q : ℕ) : ModularCurve.HeckeAlg ⧸ 𝔪))
    (ι : V →+ J) (hinj : Function.Injective ι)
    (hequiv : ∀ g : G, ∀ v : V, ι (g • v) = g • ι v)
    (htors : ∀ v : V, ι v ∈ ModularCurve.heckeTorsion J 𝔪)
    (hrank : Module.finrank k V = 2)
    (hdet : LinearMap.det (DistribSMul.toLinearMap k V φ) = (q : k))
    (hunr : ∀ σ ∈ I, ∀ v : V, σ • v = v)
    (hscalar : (∀ v : V, ι v ∈ 𝒯) → ∃ lam : k, ∀ v : V, φ • v = lam • v)
    (hq0 : (q : k) ≠ 0) (hq1 : (q : k) ≠ 1) :
    ModularCurve.HasLowerLevelTorsion S 𝔪 J₀ := by sorry
