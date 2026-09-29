-- Prove2me | Theorems.Thm_HopfAlgebra_exists_distribMulAction_withConv_equiv_of_weilRestriction_points_padic
-- name    : HopfAlgebra.exists_distribMulAction_withConv_equiv_of_weilRestriction_points_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/814c6528-81dd-55a8-be27-40a300cce032
-- title:
--   ℚ̄ₚ-points of a Weil restriction as induced Galois module
-- statement:
--   Let $p$ be a prime and write $L = \mathrm{AlgebraicClosure}\,\mathbb{Q}_p$ and $\Gamma$ for the group of $\mathbb{Q}_p$-algebra automorphisms of $L$. Let $B$ be a commutative domain which is a finite free étale $\mathbb{Z}_p$-algebra, equipped with a $B$-algebra structure on $L$ compatible with the $\mathbb{Z}_p$-structures; let $H$ be a commutative Hopf $B$-algebra, finite and free as a $B$-module and cocommutative as a $B$-coalgebra; and let $W$ be a commutative Hopf $\mathbb{Z}_p$-algebra. Assume given, for every commutative $\mathbb{Z}_p$-algebra $T$, a bijection $e_T$ from the convolution monoid of $\mathbb{Z}_p$-algebra maps $W \to T$ to the convolution monoid of $B$-algebra maps $H \to B \otimes_{\mathbb{Z}_p} T$, which is multiplicative for the convolution products, and natural in $T$: for a $\mathbb{Z}_p$-algebra map $u : T \to T'$ one has $e_{T'}(u \circ f) = (\mathrm{id}_B \otimes u) \circ e_T(f)$. The conclusion asserts the existence of an additive abelian group $P$ with a distributive $\Gamma$-action, a bijection $e_W$ from the convolution monoid of $\mathbb{Z}_p$-algebra maps $W \to L$ onto $P$, and a group homomorphism $\pi_0$ from $P$ to the additive group of the convolution monoid of $B$-algebra maps $H \to L$, such that: $e_W$ carries convolution to addition; $e_W(g) = \sigma \cdot e_W(f)$ whenever $g = \sigma \circ f$ pointwise on $W$; $\pi_0(e_W(f))$ is $e_L(f)$ followed by the map $B \otimes_{\mathbb{Z}_p} L \to L$, $b \otimes x \mapsto \mathrm{algebraMap}(b)\,x$; for every $\sigma$ fixing the image of $B$ in $L$ pointwise, every $x \in P$ and every $g$ with $g(h) = \sigma(\pi_0(x)(h))$ for all $h \in H$, one has $\pi_0(\sigma \cdot x) = g$; an $x \in P$ with $\pi_0(\sigma \cdot x) = 0$ for all $\sigma$ is $0$; and every $f$ in the convolution monoid of $B$-algebra maps $H \to L$ is $\pi_0(x)$ for some $x \in P$ with $\pi_0(\sigma \cdot x) = 0$ for every $\sigma$ moving some element of the image of $B$. (Here $0$ denotes the convolution unit, written additively.)
--
--   This is the functor-of-points description of the $L$-points of the Weil restriction to $\mathbb{Z}_p$ of a finite flat cocommutative Hopf algebra over the finite unramified extension $B$: the Galois module $W(L)$ is induced from $H(L)$ along the subgroup of $\Gamma$ fixing $B$, with $\pi_0$ the component at the given embedding $B \hookrightarrow L$. It feeds [`HopfAlgebra.exists_finiteFlat_padicInt_withConv_equiv_of_multiplicative_by_unramified_of_unitKummer`](thm.html#HopfAlgebra.exists_finiteFlat_padicInt_withConv_equiv_of_multiplicative_by_unramified_of_unitKummer), and its proof uses the existence of convolution inverses through the antipode, [`HopfAlgebra.exists_comp_antipode_convMul_eq_one`](thm.html#HopfAlgebra.exists_comp_antipode_convMul_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_distribMulAction_withConv_equiv_of_weilRestriction_points_padic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_distribMulAction_withConv_equiv_of_weilRestriction_points_padic
    (p : ℕ) [Fact p.Prime]
    (B : Type) [CommRing B] [IsDomain B] [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B] [Module.Free ℤ_[p] B]
    [Algebra.Etale ℤ_[p] B]
    [Algebra B (AlgebraicClosure ℚ_[p])] [IsScalarTower ℤ_[p] B (AlgebraicClosure ℚ_[p])]
    (H : Type) [CommRing H] [HopfAlgebra B H] [Module.Finite B H] [Module.Free B H] [Coalgebra.IsCocomm B H]
    (W : Type) [CommRing W] [HopfAlgebra ℤ_[p] W]
    (e : ∀ (T : Type) [CommRing T] [Algebra ℤ_[p] T],
      WithConv (W →ₐ[ℤ_[p]] T) ≃ WithConv (H →ₐ[B] (B ⊗[ℤ_[p]] T)))
    (he_mul : ∀ (T : Type) [CommRing T] [Algebra ℤ_[p] T] (f g : WithConv (W →ₐ[ℤ_[p]] T)),
      e T (f * g) = e T f * e T g)
    (he_nat : ∀ (T T' : Type) [CommRing T] [Algebra ℤ_[p] T] [CommRing T'] [Algebra ℤ_[p] T'] (u : T →ₐ[ℤ_[p]] T')
      (f : WithConv (W →ₐ[ℤ_[p]] T)),
      e T' (WithConv.toConv (u.comp f.ofConv))
        = WithConv.toConv ((Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f).ofConv)) :
    ∃ (P : Type) (_ : AddCommGroup P) (_ : DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) P)
      (eW : WithConv (W →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ P)
      (π₀ : P →+ Additive (WithConv (H →ₐ[B] AlgebraicClosure ℚ_[p]))),
      (∀ f g, eW (f * g) = eW f + eW g) ∧
      (∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (f g : WithConv (W →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
        (∀ x : W, g x = σ (f x)) → eW g = σ • (eW f)) ∧
      (∀ f : WithConv (W →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]),
        Additive.toMul (π₀ (eW f)) = WithConv.toConv
          ((Algebra.TensorProduct.lift (Algebra.ofId B (AlgebraicClosure ℚ_[p])) (AlgHom.id ℤ_[p] (AlgebraicClosure ℚ_[p]))
            (fun _ _ => Commute.all _ _)).comp (e (AlgebraicClosure ℚ_[p]) f).ofConv)) ∧
      (∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]), (∀ b : B, σ (algebraMap B (AlgebraicClosure ℚ_[p]) b) = algebraMap B (AlgebraicClosure ℚ_[p]) b) →
        ∀ (x : P) (g : WithConv (H →ₐ[B] AlgebraicClosure ℚ_[p])),
          (∀ h : H, g h = σ (Additive.toMul (π₀ x) h)) → π₀ (σ • x) = Additive.ofMul g) ∧
      (∀ x : P, (∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p], π₀ (σ • x) = 0) → x = 0) ∧
      (∀ f : WithConv (H →ₐ[B] AlgebraicClosure ℚ_[p]), ∃ x : P, π₀ x = Additive.ofMul f ∧
        ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p], (∃ b : B, σ (algebraMap B (AlgebraicClosure ℚ_[p]) b) ≠ algebraMap B (AlgebraicClosure ℚ_[p]) b) →
          π₀ (σ • x) = 0) := by sorry
