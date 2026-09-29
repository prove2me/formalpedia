-- Prove2me | Theorems.Thm_ModularCurve_UniformizedHeckeCurve_exists_algEquiv_realize_eventuallyEq_of_meromorphicAt_of_separatesOrbits
-- name    : ModularCurve.UniformizedHeckeCurve.exists_algEquiv_realize_eventuallyEq_of_meromorphicAt_of_separatesOrbits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/f39a906b-0892-5207-bd42-2fb9408af85d
-- title:
--   Comparison of two germwise meromorphic realisations of function fields
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$. Let $Fc_0$ be a field which is a $\mathbb{C}$-algebra, essentially of finite type over $\mathbb{C}$ and a curve over $\mathbb{C}$ in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15) (every nonzero element has a principal divisor of degree $0$, every place — a valuation subring containing $\mathbb{C}$, distinct from the whole field, with principal ideals — has residue field finite over $\mathbb{C}$, and $\Omega_{Fc_0/\mathbb{C}}$ is free of rank one), and let $U_0$ be a [`ModularCurve.UniformizedHeckeCurve`](def/ModularCurve_UniformizedHeckeCurve.html#L14) structure for $\Gamma$ on $Fc_0$, so in particular a place map $\mathrm{pt} : \mathfrak{H} \to \mathrm{Place}(\mathbb{C}, Fc_0)$ with $\mathrm{pt}\,\tau = \mathrm{pt}\,\tau'$ exactly when $\tau' \in \Gamma\tau$, a realisation $\mathrm{realize} : Fc_0 \to \mathfrak{H} \to \mathbb{C}$ whose valuation subring at $\tau$ consists of the $x$ with $\|\mathrm{realize}\,x\|$ bounded on a punctured neighbourhood of $\tau$, ramification indices, and Hecke correspondences. Assume $\mathrm{pt}$ is surjective, that $\mathrm{realize}$ is additive, multiplicative and sends $\mathbb{C}$-scalars to constants on a punctured neighbourhood of every $\tau \in \mathfrak{H}$, that elements agreeing germwise at every $\tau$ are equal, and that $\mathrm{realize}$ is complete: every $f : \mathfrak{H} \to \mathbb{C}$ which is meromorphic at each $\tau$ (after transport along `UpperHalfPlane.ofComplex`) and germwise $\Gamma$-invariant is germwise $\mathrm{realize}\,x$ for some $x$. Let $Fc$ be a second such curve over $\mathbb{C}$, essentially of finite type, together with $V : Fc \to \mathfrak{H} \to \mathbb{C}$ such that each $V\,x$ is meromorphic at every $\tau$, is germwise invariant under every $\gamma \in \Gamma$, and $V$ is germwise additive, multiplicative and constant on $\mathbb{C}$; assume $V$ separates $\Gamma$-orbits: if for all $x$ the function $\|V\,x\|$ is bounded near $\tau$ precisely when it is bounded near $\tau'$, then $\tau' = \gamma\tau$ for some $\gamma \in \Gamma$. Finally let $P$ be a type with maps $\mathrm{per} : P \to \mathfrak{H}$ and $\mathrm{bc} : P \to \mathrm{Place}(\mathbb{C}, Fc)$ such that $x$ lies in the valuation subring of $\mathrm{bc}\,p$ exactly when $\|V\,x\|$ is bounded on a punctured neighbourhood of $\mathrm{per}\,p$. Then there is a $\mathbb{C}$-algebra isomorphism $e : Fc \simeq Fc_0$ with $\mathrm{realize}(e\,x) = V\,x$ on a punctured neighbourhood of every $\tau \in \mathfrak{H}$, and such that for all $p$ and $x$, $e\,x$ lies in the valuation subring of $\mathrm{pt}(\mathrm{per}\,p)$ if and only if $x$ lies in that of $\mathrm{bc}\,p$.
--
--   This is the algebraic comparison step in the complex uniformisation of a curve by a Fuchsian-type group: two one-variable function fields over $\mathbb{C}$ realised as germs of $\Gamma$-automorphic meromorphic functions on the upper half-plane are canonically identified, compatibly with the dictionary between places and points. It is applied in the Čerednik–Drinfeld quaternionic setting to transport a `UniformizedHeckeCurve` structure along a period map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_UniformizedHeckeCurve_exists_algEquiv_realize_eventuallyEq_of_meromorphicAt_of_separatesOrbits.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology

theorem ModularCurve.UniformizedHeckeCurve.exists_algEquiv_realize_eventuallyEq_of_meromorphicAt_of_separatesOrbits
    (Γ : Subgroup (GL (Fin 2) ℝ))

    (Fc₀ : Type) [Field Fc₀] [Algebra ℂ Fc₀] [AlgebraicCurve.IsCurveOver ℂ Fc₀] [Algebra.EssFiniteType ℂ Fc₀]
    (U₀ : ModularCurve.UniformizedHeckeCurve Γ Fc₀)
    (hsurj : Function.Surjective U₀.pt)
    (hadd₀ : ∀ (x y : Fc₀) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U₀.realize (x + y) z = U₀.realize x z + U₀.realize y z)
    (hmul₀ : ∀ (x y : Fc₀) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U₀.realize (x * y) z = U₀.realize x z * U₀.realize y z)
    (hconst₀ : ∀ (c : ℂ) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U₀.realize (algebraMap ℂ Fc₀ c) z = c)
    (hinj₀ : ∀ x y : Fc₀, (∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U₀.realize x z = U₀.realize y z) → x = y)
    (hcomplete₀ : ∀ f : UpperHalfPlane → ℂ,
      (∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => f (UpperHalfPlane.ofComplex z)) (τ : ℂ)) →
      (∀ γ ∈ Γ, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, f (γ • z) = f z) →
      ∃ x : Fc₀, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U₀.realize x z = f z)

    (Fc : Type) [Field Fc] [Algebra ℂ Fc] [AlgebraicCurve.IsCurveOver ℂ Fc] [Algebra.EssFiniteType ℂ Fc]
    (V : Fc → UpperHalfPlane → ℂ)
    (hmero : ∀ (x : Fc) (τ : UpperHalfPlane), MeromorphicAt (fun z : ℂ => V x (UpperHalfPlane.ofComplex z)) (τ : ℂ))
    (hinv : ∀ x : Fc, ∀ γ ∈ Γ, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, V x (γ • z) = V x z)
    (hadd : ∀ (x y : Fc) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, V (x + y) z = V x z + V y z)
    (hmul : ∀ (x y : Fc) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, V (x * y) z = V x z * V y z)
    (hconst : ∀ (c : ℂ) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, V (algebraMap ℂ Fc c) z = c)
    (hsep : ∀ τ τ' : UpperHalfPlane,
      (∀ x : Fc, Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : UpperHalfPlane => ‖V x z‖) ↔
        Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ') (fun z : UpperHalfPlane => ‖V x z‖)) →
      ∃ γ ∈ Γ, γ • τ = τ')

    (P : Type) (per : P → UpperHalfPlane) (bc : P → AlgebraicCurve.Place ℂ Fc)
    (hbc : ∀ (p : P) (x : Fc), x ∈ (bc p).toValuationSubring ↔
      Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] (per p)) (fun z : UpperHalfPlane => ‖V x z‖)) :
    ∃ e : Fc ≃ₐ[ℂ] Fc₀,
      (∀ (x : Fc) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U₀.realize (e x) z = V x z) ∧
      (∀ (p : P) (x : Fc), e x ∈ (U₀.pt (per p)).toValuationSubring ↔ x ∈ (bc p).toValuationSubring) := by sorry
