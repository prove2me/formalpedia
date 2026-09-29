-- Prove2me | Theorems.Thm_HopfAlgebra_exists_field_lineAction_of_finite_flat_of_inertiaSimple_step
-- name    : HopfAlgebra.exists_field_lineAction_of_finite_flat_of_inertiaSimple_step
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/f6f5ff2b-9c11-53cd-8c3d-c392b76e7a05
-- title:
--   A finite field acting on an inertia-simple step of points
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and let $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) be the subring of $\mathbf Q$ of rationals whose denominator is coprime to $p$. Let $H$ be a commutative ring carrying the structure of a Hopf algebra over $R$ that is module-finite and flat over $R$ and whose comultiplication is cocommutative, and let $G =$ `WithConv (H →ₐ[R] AlgebraicClosure ℚ)` be the monoid of $R$-algebra homomorphisms $H \to \overline{\mathbf Q}$ under convolution; assume $f^p = 1$ for every $f \in G$. Let $P$ be a valuation subring of $\overline{\mathbf Q}$ with $p$ in its set of nonunits, and write $I_P$ for the image in $\operatorname{Aut}_{\mathbf Q}(\overline{\mathbf Q})$ of the inertia subgroup of $P$ inside its decomposition subgroup. Let $K \le K'$ be submonoids of $G$, each stable under $I_P$ in the sense that whenever $\sigma \in I_P$, $f$ lies in the submonoid and $g \in G$ satisfies $g(h) = \sigma(f(h))$ for all $h \in H$, then $g$ lies in the submonoid; assume the step is $I_P$-simple: every $I_P$-stable submonoid $S$ with $K \le S \le K'$ equals $K$ or $K'$. Let $s \geq 1$ with $\operatorname{card} K' = p^s \cdot \operatorname{card} K$. Then there exist a finite field $F$ and a map $\mathrm{act} : F \to G \to G$ such that $|F| = p^s$ and, writing $a \cdot f$ for $\mathrm{act}\,a\,f$ and $\equiv$ for equality up to right multiplication by an element of $K$: $a \cdot f \in K'$ for $f \in K'$; $a \cdot (fk) \equiv a \cdot f$ for $k \in K$; $a \cdot (fg) \equiv (a \cdot f)(a \cdot g)$, $(a+b) \cdot f \equiv (a \cdot f)(b \cdot f)$, $(ab) \cdot f \equiv a \cdot (b \cdot f)$ and $1 \cdot f \equiv f$ for $f, g \in K'$ and $a, b \in F$; for $\sigma \in I_P$, $a \in F$, $f \in K'$ and $g \in G$ with $g(h) = \sigma(f(h))$ for all $h$, there is $k \in K$ with $((a \cdot g)k)(h) = \sigma((a \cdot f)(h))$ for all $h \in H$; and for every $f_0 \in K' \setminus K$ each $g \in K'$ satisfies $g \equiv a \cdot f_0$ for some $a \in F$, with $a$ uniquely determined.
--
--   This is Schur's lemma for the action of inertia at $p$ on a simple step $K \le K'$ in the points of a finite flat group scheme, recorded directly in the convolution monoid rather than on a quotient: the quotient $K'/K$ is a line over the finite field $F = \operatorname{End}_{I_P}(K'/K)$ of $p^s$ elements, and the inertia action is $F$-linear. It is used in the construction of a normal-form $F$-vector-space model for such a step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_field_lineAction_of_finite_flat_of_inertiaSimple_step.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_field_lineAction_of_finite_flat_of_inertiaSimple_step
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (K K' : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))
    (hKK' : K ≤ K')
    (hK : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K,
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K))
    (hK' : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K'))
    (hstep : ∀ S : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      K ≤ S → S ≤ K' →
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ S,
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → g ∈ S) →
      S = K ∨ S = K')
    (s : ℕ) [NeZero s] (hcard : Nat.card K' = p ^ s * Nat.card K) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F)
      (act : F → WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →
        WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      Fintype.card F = p ^ s ∧
      (∀ a : F, ∀ f ∈ K', act a f ∈ K') ∧
      (∀ a : F, ∀ f ∈ K', ∀ k ∈ K, ∃ k' ∈ K, act a (f * k) = act a f * k') ∧
      (∀ a : F, ∀ f ∈ K', ∀ g ∈ K', ∃ k ∈ K, act a (f * g) = act a f * act a g * k) ∧
      (∀ a b : F, ∀ f ∈ K', ∃ k ∈ K, act (a + b) f = act a f * act b f * k) ∧
      (∀ a b : F, ∀ f ∈ K', ∃ k ∈ K, act (a * b) f = act a (act b f) * k) ∧
      (∀ f ∈ K', ∃ k ∈ K, act 1 f = f * k) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : F, ∀ f ∈ K',
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → ∃ k ∈ K, ∀ h : H, (act a g * k) h = σ ((act a f) h)) ∧
      (∀ f₀ ∈ K', f₀ ∉ K → ∀ g ∈ K', ∃ a : F, ∃ k ∈ K, g = act a f₀ * k) ∧
      (∀ f₀ ∈ K', f₀ ∉ K → ∀ a b : F, (∃ k ∈ K, act a f₀ = act b f₀ * k) → a = b) := by sorry
