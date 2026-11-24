-- Prove2me | Theorems.Thm_HodgeComputer_Formal_ResidueTransport_injective_of_coordinate_derivations
-- name    : HodgeComputer.Formal.ResidueTransport.injective_of_coordinate_derivations
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T03:22:13.229791+00:00
-- url     : https://prove2.me/theorems/18d7bfdb-1a4c-4bb5-b9ee-d27a51209fd0
-- title:
--   Algebraic independence from dual coordinate derivations
-- statement:
--   Let $k$ and $K$ be fields with $\operatorname{char}(k) = 0$, $\sigma$ a finite type, $\varphi : k \to K$ a field homomorphism, $x : \sigma \to K$ a tuple of elements, and $D : \sigma \to \operatorname{Der}_{\mathbb{Z}}(K, K)$ a family of derivations such that
--
--   $$D_i(\varphi(c)) = 0 \quad (\forall i \in \sigma,\, c \in k) \qquad\text{and}\qquad D_i(x_j) = \delta_{ij} \quad (\forall i, j \in \sigma).$$
--
--   Then the polynomial evaluation homomorphism $\operatorname{eval}_{2,\varphi,x} : k[X_i : i \in \sigma] \to K$ is injective.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/ResidueTransport/CoordinateIndependence.lean

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Derivation.Basic
set_option autoImplicit false

theorem HodgeComputer.Formal.ResidueTransport.injective_of_coordinate_derivations
    {k K σ : Type*} [Field k] [Field K] [CharZero k]
    [Fintype σ] [DecidableEq σ]
    (φ : k →+* K) (x : σ → K) (D : σ → Derivation ℤ K K)
    (hC : ∀ i c, D i (φ c) = 0)
    (hx : ∀ i j, D i (x j) = if j = i then 1 else 0) :
    Function.Injective (MvPolynomial.eval₂Hom φ x) := by sorry
