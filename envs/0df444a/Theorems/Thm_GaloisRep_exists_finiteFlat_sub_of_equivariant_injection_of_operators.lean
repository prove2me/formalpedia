-- Prove2me | Theorems.Thm_GaloisRep_exists_finiteFlat_sub_of_equivariant_injection_of_operators
-- name    : GaloisRep.exists_finiteFlat_sub_of_equivariant_injection_of_operators
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/29ec10da-eddf-5738-acce-e77d1d2bb1b9
-- title:
--   Finite flat sub-models with a family of operators
-- statement:
--   Fix a natural number $p$ and write $R = \mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$. Let $G$ be a commutative ring carrying a Hopf algebra structure over $R$ which is finite and flat as an $R$-module and whose comultiplication is cocommutative. Let $M$ be an additive commutative group with a distributive action of $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$, written as $\mathbb{Q}$-algebra self-equivalences of `AlgebraicClosure ℚ`, and let $e$ be a bijection from the set of $R$-algebra maps $G \to \overline{\mathbb{Q}}$, taken with its convolution multiplication via the type synonym `WithConv`, onto $M$ such that $e(f\cdot g) = e f + e g$, and such that whenever two points satisfy $g(x) = \sigma(f(x))$ for all $x \in G$ one has $e g = \sigma \cdot e f$. Let $T$ be a type, $\mathrm{act} : T \to \mathrm{End}_{+}(M)$ a family of additive endomorphisms, and $\varphi : T \to \mathrm{End}_{R\text{-alg}}(G)$ a family of $R$-algebra endomorphisms of $G$ such that each $\varphi_t$ carries the kernel of the counit of $G$ into itself (stated as the inclusion of that kernel in its preimage under $\varphi_t$), and such that whenever $g(x) = f(\varphi_t(x))$ for all $x \in G$ one has $e g = \mathrm{act}_t(e f)$. Let $N$ be a further additive commutative group with a distributive action of $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$, let $\iota : N \to M$ be an injective additive map with $\iota(\sigma \cdot n) = \sigma \cdot \iota(n)$, and let $\mathrm{actN} : T \to \mathrm{End}_{+}(N)$ satisfy $\iota(\mathrm{actN}_t(n)) = \mathrm{act}_t(\iota(n))$. The conclusion asserts the existence of a commutative ring $H$ with a Hopf algebra structure over $R$, finite and flat as an $R$-module and cocommutative, together with a bijection $e'$ from the $R$-algebra maps $H \to \overline{\mathbb{Q}}$ under convolution onto $N$ satisfying the same two conditions (additivity for the convolution product, and Galois equivariance in the same pointwise formulation), and a family $\varphi' : T \to \mathrm{End}_{R\text{-alg}}(H)$ each member of which carries the kernel of the counit of $H$ into itself and realises $\mathrm{actN}_t$ on points: if $g(x) = f(\varphi'_t(x))$ for all $x \in H$, then $e' g = \mathrm{actN}_t(e' f)$.
--
--   This is the schematic closure of a Galois-stable subgroup of the generic fibre inside a finite flat commutative group scheme over $\mathbb{Z}_{(p)}$, in Hopf-algebra form and with the additional assertion that endomorphisms preserving the subgroup descend to the closure. It is used by [`ModularCurve.exists_finiteFlat_model_heckeTorsion_jZero_of_not_dvd`](thm.html#ModularCurve.exists_finiteFlat_model_heckeTorsion_jZero_of_not_dvd), where $G$ models the $p$-torsion of a Jacobian, the operators indexed by $T$ are Hecke operators, and $N$ is the part of the torsion cut out by a maximal ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_exists_finiteFlat_sub_of_equivariant_injection_of_operators.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FiniteFlat_ClosureHopf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.exists_finiteFlat_sub_of_equivariant_injection_of_operators (p : ℕ)
    (G : Type) [CommRing G] [HopfAlgebra (GaloisRep.ratLocalizedAt p) G]
    [Module.Finite (GaloisRep.ratLocalizedAt p) G] [Module.Flat (GaloisRep.ratLocalizedAt p) G]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) G]
    {M : Type} [AddCommGroup M] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (e : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : G, g x = σ (f x)) → e g = σ • (e f))
    {T : Type} (act : T → M →+ M)
    (φ : T → (G →ₐ[GaloisRep.ratLocalizedAt p] G))
    (hφ_aug : ∀ t : T,
      RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) G) ≤
        (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) G)).comap (φ t))
    (hφ : ∀ (t : T) (f g : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : G, g x = f (φ t x)) → e g = act t (e f))
    {N : Type} [AddCommGroup N] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (ι : N →+ M) (hι : Function.Injective ι)
    (hι_eq : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : N), ι (σ • n) = σ • (ι n))
    (actN : T → N →+ N) (hι_act : ∀ (t : T) (n : N), ι (actN t n) = act t (ι n)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧ Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e' : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N,
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ x : H, g x = σ (f x)) → e' g = σ • (e' f)) ∧
        ∃ φ' : T → (H →ₐ[GaloisRep.ratLocalizedAt p] H),
          (∀ t : T,
            RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H) ≤
              (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H)).comap (φ' t)) ∧
          ∀ (t : T) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
            (∀ x : H, g x = f (φ' t x)) → e' g = actN t (e' f) := by sorry
