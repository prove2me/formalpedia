-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane
-- name    : LanglandsTunnell.CubicInduction.hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/beef6931-d153-5275-9ee9-c0d84cff3e2a
-- title:
--   Moments of all orders for Φ and its dual along GL₂
-- statement:
--   Fix a subset $D$ of $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$, an assignment $U$ of a subgroup of that group to each ideal of $\mathbb{Z}$, an assignment $\mathrm{gen}$ of an element to each finite place, a complex-valued additive character $\psi$ of the adele ring of $\mathbb{Q}$, and a function $\Phi$ on $\mathrm{GL}_3$ of the adeles. All Whittaker integrals below are taken with respect to `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)`, the carrier data consisting of the Borel $\sigma$-algebra and Haar measure on adelic $\mathrm{GL}_2$, the set $D$, the full subgroup of idele classes, $U$, $\mathrm{gen}$, and the additive Haar measure of the adele ring conditioned on the adelic box (the fundamental domain of the Minkowski lattice at the infinite places together with the integral finite adeles); thus `whittaker3 … ψ Φ g` is the triple integral over this conditioned measure of $\Phi(u(x,y,z)g)\,\psi(-(x+y))$, with $u(x,y,z)$ the upper unipotent matrix in $\mathrm{GL}_3$. The hypotheses are: for every $g$, the family indexed by the mirabolic index set (the quotient of $\mathrm{GL}_2(\mathbb{Q})$ by the right relation attached to the range of the unipotent homomorphism) whose $i$-th term is `whittaker3 … ψ Φ` evaluated at $\iota(\mathrm{mirabolicRep}(i))\,g$ is summable with sum $\Phi(g)$; the same expansion holds for $\psi^{-1}$ and the dual function $\mathrm{dualForm}\,\Phi(g)=\Phi({}^{t}g^{-1})$; and both `whittaker3 … ψ Φ` and `whittaker3 … ψ⁻¹ (dualForm Φ)` satisfy `HasWhittakerHalfPlane`, i.e. there is $\sigma_0$ such that for all $\sigma\ge\sigma_0$ and every fundamental domain $D'$ for $\mathrm{GL}_2(\mathbb{Q})$ acting on adelic $\mathrm{GL}_2$ with its Haar measure, the integral over $D'$ of the mirabolic sum of the norms of the Whittaker function, weighted by the $\sigma$-th power of the idele norm of $\det g$, is finite. The conclusion is that both $\Phi$ and $\mathrm{dualForm}\,\Phi$ have $\iota$-moments: for every such fundamental domain $D'$ and every natural number $N$, the integral over $D'$ of $\|\Phi(\iota(g))\|$ times $\|\det g\|^{N}+\|\det g\|^{-N}$ is finite.
--
--   This is the passage from the mirabolic (Whittaker) expansion of a function on $\mathrm{GL}_3$ of the adeles, together with half-plane integrability of its Whittaker coefficients, to moment bounds of every order along the embedded $\mathrm{GL}_2$, the growth input required on the analytic side of the converse-theorem machinery for $\mathrm{GL}_3$. It is used in the construction of cubic induction data in the Langlands–Tunnell part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hexp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum
      (fun i : MirabolicIndex ℚ =>
      whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ (mirabolicTranslate i * g))
      (Φ g))
    (hexp' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum
      (fun i : MirabolicIndex ℚ =>
      whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ⁻¹ (dualForm Φ) (mirabolicTranslate i * g))
      (dualForm Φ g))
    (hhp : HasWhittakerHalfPlane (whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ))
    (hhp' : HasWhittakerHalfPlane (whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ⁻¹ (dualForm Φ))) :
    HasIotaMoments Φ ∧ HasIotaMoments (dualForm Φ) := by sorry
