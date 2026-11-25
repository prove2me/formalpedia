-- Prove2me | Theorems.Thm_LinearMap_det_eq_of_alternating_pairing_map_eq_pow
-- name    : LinearMap.det_eq_of_alternating_pairing_map_eq_pow
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T17:13:32.998398+00:00
-- url     : https://prove2.me/theorems/0854e83a-e008-43a7-9592-714bb4f8bb6d
-- title:
--   Rank-2 symplectic similitudes: if an endomorphism $A$ of a free rank-2 $\mathbb Z/n$-module multiplies an alternating nondegenerate pairing by the power $d$, then $\det A = d$ in $\mathbb Z/n$
-- statement:
--   Let $n \ge 1$ and let $G$ be a free $\mathbb Z/n\mathbb Z$-module of rank $2$ (given together with a basis $b_0, b_1$). Let $M$ be a commutative group, written multiplicatively, and let $e : G \times G \to M$ be a pairing which is
--
--   - bimultiplicative: $e(P + P', Q) = e(P, Q)\, e(P', Q)$ and $e(P, Q + Q') = e(P, Q)\, e(P, Q')$ for all $P, P', Q, Q' \in G$;
--   - alternating: $e(P, P) = 1$ for all $P \in G$;
--   - nondegenerate: if $e(P, Q) = 1$ for all $P \in G$, then $Q = 0$.
--
--   Let $A : G \to G$ be a $\mathbb Z/n\mathbb Z$-linear map and $d \ge 0$ an integer such that
--
--   $$e(AP, AQ) = e(P, Q)^d \quad \text{for all } P, Q \in G .$$
--
--   Then
--
--   $$\det A = d \quad \text{in } \mathbb Z/n\mathbb Z .$$
--
--   Role: this is the linear-algebra step behind the statement that the determinant of the mod-$n$ Galois representation of an elliptic curve is the mod-$n$ cyclotomic character: the Weil pairing $e_n : E[n] \times E[n] \to \mu_n$ is bimultiplicative, alternating, nondegenerate and Galois-equivariant, so $e_n(\sigma P, \sigma Q) = \sigma(e_n(P,Q)) = e_n(P,Q)^{\chi(\sigma)}$, and the theorem gives $\det \rho_{E,n}(\sigma) = \chi(\sigma) \bmod n$. In the language of symplectic groups: on a rank-$2$ module every alternating nondegenerate form is a multiple of the determinant form, so the multiplier of a similitude equals its determinant ($\mathrm{GSp}_2 = \mathrm{GL}_2$).
--
--   **Formalization Note**: `Module.Basis (Fin 2) (ZMod n) G` is a basis of $G$ indexed by $\{0, 1\}$, so $G$ is free of rank $2$; `[NeZero n]` is $n \ge 1$. The pairing is an arbitrary function `e : G → G → M` into a commutative group `M`; the hypotheses `hadd_l`, `hadd_r`, `hself`, `hnd` are bimultiplicativity in each variable, the alternating property and nondegeneracy (in the second variable; with the alternating property this is equivalent to nondegeneracy in the first). `LinearMap.det A` is the determinant of the $\mathbb Z/n$-linear endomorphism `A`, and `(d : ZMod n)` is the residue of the natural number $d$. All types are in `Type`.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Section III.8 (Proposition 8.1 and Corollary 8.1.1: the Weil pairing and det of the mod-n representation), doi:10.1007/978-0-387-09494-6

import Mathlib

set_option autoImplicit false

theorem LinearMap.det_eq_of_alternating_pairing_map_eq_pow
    {n : ℕ} [NeZero n] {G : Type} [AddCommGroup G] [Module (ZMod n) G]
    {M : Type} [CommGroup M] (e : G → G → M)
    (hadd_l : ∀ P P' Q, e (P + P') Q = e P Q * e P' Q)
    (hadd_r : ∀ P Q Q', e P (Q + Q') = e P Q * e P Q')
    (hself : ∀ P, e P P = 1) (hnd : ∀ Q, (∀ P, e P Q = 1) → Q = 0)
    (b : Module.Basis (Fin 2) (ZMod n) G) (A : G →ₗ[ZMod n] G) (d : ℕ)
    (hA : ∀ P Q, e (A P) (A Q) = e P Q ^ d) :
    LinearMap.det A = (d : ZMod n) := by
  sorry
