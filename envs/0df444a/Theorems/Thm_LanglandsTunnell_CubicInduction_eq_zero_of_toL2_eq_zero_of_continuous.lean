-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_toL2_eq_zero_of_continuous
-- name    : LanglandsTunnell.CubicInduction.eq_zero_of_toL2_eq_zero_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/1b329002-f4ea-5432-916d-e08c2f06e232
-- title:
--   Continuous automorphic form with vanishing L²-class is zero
-- statement:
--   Let $\omega\colon(\mathbb{A}_{\mathbb{Q}})^{\times}\to\mathbb{C}^{\times}$ be a group homomorphism on the units of the adele ring of $\mathbb{Q}$, let $a,b$ be reals, and let $\Phi_0$ be a subset of $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ which is a slab domain for $(a,b)$, i.e. $0<a$, $a<b$, and $\Phi_0$ is a fundamental domain for the left translation action of the image of $\mathrm{GL}_3(\mathbb{Q})$ (under `globalPointsGL`) with respect to `slabMeasure a b`, the adelic Haar measure of $\mathrm{GL}_3$ restricted to the determinant slab $\{g : \|\det g\|_{\mathbb{A}}\in[a,b]\}$. Let $F\colon \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ lie in `automorphicSubmodule ω a b Φ₀`, that is: $F(\gamma g)=F(g)$ for all $\gamma\in\mathrm{GL}_3(\mathbb{Q})$ and all $g$; $F(zg)=\omega(z)F(g)$ for every idele unit $z$, acting through the central scalar embedding; and $F$ is in $L^2$ of `domainMeasure a b Φ₀`, the slab measure further restricted to $\Phi_0$. Assume moreover that $F$ is continuous and that its class in $L^2(\mathrm{domainMeasure}\ a\ b\ \Phi_0)$, formed by `toL2`, is zero. Then $F=0$ as a function on all of $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$.
--
--   This is the passage from the $L^2$-class of an automorphic function on the slab fundamental domain back to the function itself, valid for continuous representatives; it lets identities proved in the Hilbert space `Carrier a b Φ₀` be read off pointwise. It is used in the spectral arguments on the slab $L^2$ space (Casimir eigenvector constructions) and in the vanishing statement for products of Whittaker functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_eq_zero_of_toL2_eq_zero_of_continuous.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2

theorem
LanglandsTunnell.CubicInduction.eq_zero_of_toL2_eq_zero_of_continuous
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ automorphicSubmodule ω a b Φ₀) (_hFc : Continuous F)
    (_h0 : toL2 ω a b Φ₀ ⟨F, hF⟩ = 0) :
    F = 0 := by sorry
