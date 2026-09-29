-- Prove2me | Theorems.Thm_HopfAlgebra_FVect_exists_profile_of_isFCompatible
-- name    : HopfAlgebra.FVect.exists_profile_of_isFCompatible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/598a2566-fbea-5194-aac5-1f9803f814d3
-- title:
--   Raynaud profile of an F-equivariant map of Hopf orders
-- statement:
--   Let $R'$ be a discrete valuation ring of characteristic zero (a local domain with its discrete valuation ring structure), $p$ a prime and $r \ge 1$, and let $F$ be a finite field with $\#F = p^r$, with $p^r - 1$ a unit in $R'$. Fix a character $\chi : F^\times \to (R')^\times$ and a ring map $\iota : F \to R'/\mathfrak m$ with $\chi(l) \equiv \iota(l)$ modulo $\mathfrak m$ for all $l \in F^\times$. Let $B$ be a Hopf $R'$-algebra, finite and free of rank $p^r$, equipped with a map $\mathrm{act} : F \to (B \to_{\mathrm{bialg}} B)$ sending $1$ to the identity, multiplicative ($\mathrm{act}(ab) = \mathrm{act}(a) \circ \mathrm{act}(b)$) and additive in the convolution sense ($\mathrm{act}(a+b)$ is the composite of the comultiplication, $\mathrm{act}(a) \otimes \mathrm{act}(b)$ and the multiplication of $B$); let $X : \mathrm{Fin}\,r \to B$ and $\delta : \mathrm{Fin}\,r \to R'$ satisfy $\mathrm{act}(l)(X_i) = \chi(l)^{p^i} X_i$ for $l \in F^\times$, $X_i^p = \delta_i X_{i+1}$ (indices in $\mathrm{Fin}\,r$, hence cyclically), $\delta_i \mid p$, $\varepsilon(X_i) = 0$, and let the monomials $\prod_i X_i^{d_i}$, $d \in (\mathrm{Fin}\,p)^{\mathrm{Fin}\,r}$, form an $R'$-basis of $B$. Let $(B', \mathrm{act}', X', \delta')$ satisfy the same hypotheses with the same $\chi$. Let $u : B \to B'$ be an injective bialgebra map with $u \circ \mathrm{act}(l) = \mathrm{act}'(l) \circ u$ for all $l \in F$. Then there is $a : \mathrm{Fin}\,r \to \mathbb Z$ with $a_i \ge 0$ and $v(\delta_i) = p\,a_i + v(\delta'_i) - a_{i+1}$ for all $i$, where $v$ denotes the normalised additive valuation of $R'$ read as a natural number, and $u$ is bijective if and only if $a = 0$.
--
--   This is the comparison of two $F$-vector Hopf orders given in Raynaud's normal form: an equivariant injection between them is recorded by a non-negative profile $a$ relating the valuations of the two systems of constants $\delta_i$, $\delta'_i$, and the injection is an isomorphism exactly when the profile vanishes. It is used in the proof that a Hopf order contained in another and stable under the $F$-action coincides with it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_FVect_exists_profile_of_isFCompatible.lean

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.Dimension.Free

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem HopfAlgebra.FVect.exists_profile_of_isFCompatible
    (R' : Type u) [CommRing R'] [IsLocalRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [CharZero R']
    (p r : ℕ) [Fact p.Prime] [NeZero r]
    (F : Type*) [Field F] [Fintype F] (hF : Fintype.card F = p ^ r)
    (hq : IsUnit ((p ^ r : R') - 1))
    (χ : Fˣ →* R'ˣ) (ι : F →+* IsLocalRing.ResidueField R')
    (hχ : ∀ l : Fˣ, IsLocalRing.residue R' (χ l : R') = ι l)
    (B : Type v) [CommRing B] [HopfAlgebra R' B] [Module.Finite R' B] [Module.Free R' B]
    (hrank : Module.finrank R' B = p ^ r)
    (act : F → (B →ₐc[R'] B))
    (act_one : act 1 = BialgHom.id R' B)
    (act_mul : ∀ a b, act (a * b) = (act a).comp (act b))
    (act_add : ∀ a b, ((act (a + b) : B →ₐ[R'] B).toLinearMap) =
      LinearMap.mul' R' B ∘ₗ TensorProduct.map (act a : B →ₐ[R'] B).toLinearMap (act b : B →ₐ[R'] B).toLinearMap
        ∘ₗ Coalgebra.comul)
    (X : Fin r → B) (δ : Fin r → R')
    (h1 : ∀ i (l : Fˣ), (act l) (X i) = (((χ ^ p ^ (i : ℕ)) l : R'ˣ) : R') • X i)
    (h2 : ∀ i, X i ^ p = δ i • X (i + 1))
    (b : Module.Basis (Fin r → Fin p) R' B) (hb : ∀ d, b d = ∏ i, X i ^ (d i : ℕ))
    (h4 : ∀ i, δ i ∣ (p : R'))
    (h5 : ∀ i, Coalgebra.counit (R := R') (X i) = 0)
    (B' : Type v) [CommRing B'] [HopfAlgebra R' B'] [Module.Finite R' B'] [Module.Free R' B']
    (hrank' : Module.finrank R' B' = p ^ r)
    (act' : F → (B' →ₐc[R'] B'))
    (act_one' : act' 1 = BialgHom.id R' B')
    (act_mul' : ∀ a b, act' (a * b) = (act' a).comp (act' b))
    (act_add' : ∀ a b, ((act' (a + b) : B' →ₐ[R'] B').toLinearMap) =
      LinearMap.mul' R' B' ∘ₗ TensorProduct.map (act' a : B' →ₐ[R'] B').toLinearMap (act' b : B' →ₐ[R'] B').toLinearMap
        ∘ₗ Coalgebra.comul)
    (X' : Fin r → B') (δ' : Fin r → R')
    (h1' : ∀ i (l : Fˣ), (act' l) (X' i) = (((χ ^ p ^ (i : ℕ)) l : R'ˣ) : R') • X' i)
    (h2' : ∀ i, X' i ^ p = δ' i • X' (i + 1))
    (b' : Module.Basis (Fin r → Fin p) R' B') (hb' : ∀ d, b' d = ∏ i, X' i ^ (d i : ℕ))
    (h4' : ∀ i, δ' i ∣ (p : R'))
    (h5' : ∀ i, Coalgebra.counit (R := R') (X' i) = 0)
    (u : B →ₐc[R'] B')
    (hu : ∀ l : F, u.comp (act l) = (act' l).comp u)
    (hu_inj : Function.Injective u) :
    ∃ a : Fin r → ℤ, (∀ i, 0 ≤ a i) ∧
      (∀ i, ((IsDiscreteValuationRing.addVal R' (δ i)).toNat : ℤ) =
        p * a i + ((IsDiscreteValuationRing.addVal R' (δ' i)).toNat : ℤ) - a (i + 1)) ∧
      (Function.Bijective u ↔ ∀ i, a i = 0) := by sorry
