-- Prove2me | Theorems.Thm_GaloisRep_exists_hopfAlgebra_withConv_equiv_of_ordinary_of_unitKummer_decomposition
-- name    : GaloisRep.exists_hopfAlgebra_withConv_equiv_of_ordinary_of_unitKummer_decomposition
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/a55172cf-6d62-5999-bbbc-ad84eea51574
-- title:
--   Unit-Kummer ordinary Galois modules from finite flat ℤ₍ₚ₎-Hopf algebras
-- statement:
--   Let $p$ be an odd prime, $N$ a natural number, and $E$ a finite abelian group carrying an action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ by additive maps, with $p^N x = 0$ for all $x \in E$ and with the action of finite level, in the sense that some intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$ of finite degree over $\mathbb Q$ has its fixing subgroup acting trivially on $E$. Let $P$ be a valuation subring of $\overline{\mathbb Q}$ in which $p$ is a nonunit, and let $E_1 \le E$ be an additive subgroup stable under the decomposition subgroup of $P$ over $\mathbb Q$, such that every $\tau$ in the inertia subgroup of $P$ over $\mathbb Q$ (the image of `inertiaSubgroup` in the decomposition group) acting on $p^N$-th roots of unity by $\xi \mapsto \xi^{c}$ acts on $E_1$ by multiplication by $c$, and such that $\tau \cdot y - y \in E_1$ for all $y \in E$ and all inertia elements $\tau$. Let $\zeta$ be a primitive $p^N$-th root of unity, and let $u, \beta : \mathrm{Fin}\,t \to \overline{\mathbb Q}$ satisfy $P$-valuation $1$ for each $u_i$, invariance of each $u_i$ under inertia, and $\beta_i^{p^N} = u_i$. Let $\varphi_i : E \to E$ ($i \in \mathrm{Fin}\,t$) be additive maps with image in $E_1$ and vanishing on $E_1$, and assume the inertia cocycle decomposes along them: whenever $\tau$ lies in inertia and fixes all $p^N$-th roots of unity, and $\tau(\beta_i) = \zeta^{k_i}\beta_i$ for all $i$, then $\tau \cdot x - x = \sum_i k_i\,\varphi_i(x)$ for all $x \in E$. The conclusion asserts the existence of a commutative ring $H$ with a Hopf algebra structure over the subring $\mathbb Z_{(p)} \subset \mathbb Q$ of rationals whose denominator is coprime to $p$ ([`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8)), finite and flat as a $\mathbb Z_{(p)}$-module and cocommutative as a coalgebra, together with a bijection $e$ from the $\mathbb Z_{(p)}$-algebra homomorphisms $H \to \overline{\mathbb Q}$ in their `WithConv` multiplicative structure onto $E$ which turns that multiplication into addition, $e(fg) = e(f) + e(g)$, and is Galois-equivariant in the sense that $e(g) = \sigma \cdot e(f)$ whenever $g = \sigma \circ f$ pointwise on $H$.
--
--   This is the module-theoretic form of the implication 'peu ramifié (multiplicative-by-unramified with unit-Kummer inertia cocycle) implies finite flat', in the shape used by the project for flatness: a finite flat cocommutative Hopf algebra over $\mathbb Z_{(p)}$ whose $\overline{\mathbb Q}$-points recover the given Galois module. It is the global input to [`GaloisRepAdic.isFlatAt_of_ordinary_of_unitKummer_decomposition`](thm.html#GaloisRepAdic.isFlatAt_of_ordinary_of_unitKummer_decomposition), and is obtained by realising the local module over $\mathbb Z_p$, forming the étale $\mathbb Q$-Hopf algebra of the global module, and glueing the two descriptions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_exists_hopfAlgebra_withConv_equiv_of_ordinary_of_unitKummer_decomposition.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRep.exists_hopfAlgebra_withConv_equiv_of_ordinary_of_unitKummer_decomposition
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (N : ℕ)
    (E : Type) [AddCommGroup E] [Finite E]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) E]
    (hE : ∀ x : E, (p ^ N) • x = 0)
    (hlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, ∀ x : E, s • x = x)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (E₁ : AddSubgroup E)
    (hE₁D : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ y ∈ E₁, σ • y ∈ E₁)
    (hE₁I : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ ^ c) → ∀ y ∈ E₁, τ • y = c • y)
    (hEI : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ y : E, τ • y - y ∈ E₁)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N))
    {t : ℕ} (u β : Fin t → AlgebraicClosure ℚ)
    (hu : ∀ i, P.valuation (u i) = 1) (huI : ∀ i, ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (u i) = u i)
    (hβ : ∀ i, β i ^ p ^ N = u i)
    (φ : Fin t → (E →+ E)) (hφ₁ : ∀ i x, φ i x ∈ E₁) (hφ₀ : ∀ i, ∀ y ∈ E₁, φ i y = 0)
    (hdec : ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
      ∀ k : Fin t → ℕ, (∀ i, τ (β i) = ζ ^ (k i) * β i) → ∀ x : E, τ • x - x = ∑ i, (k i) • φ i x) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ E,
        (∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          e (f * g) = e f + e g) ∧
        ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by sorry
