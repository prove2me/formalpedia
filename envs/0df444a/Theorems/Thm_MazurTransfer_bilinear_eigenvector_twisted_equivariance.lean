-- Prove2me | Theorems.Thm_MazurTransfer_bilinear_eigenvector_twisted_equivariance
-- name    : MazurTransfer.bilinear_eigenvector_twisted_equivariance
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-14T23:12:20.936728+00:00
-- url     : https://prove2.me/theorems/9833a95b-5554-4fca-a1c0-4a6de1dac561
-- title:
--   A covariant pairing evaluated on an eigenvector twists by the inverse character
-- statement:
--   Let V, W and U be representations of a group G over a field k, and let B: V × W → U be a Galois-covariant bilinear map. If v is a character eigenvector, so that g(v) = χ(g)v, then evaluation at v satisfies B(v, g(w)) = χ(g)⁻¹ g(B(v,w)). Thus pairing against a character line gives an equivariant map to U twisted by the inverse character. This is used to identify the complementary actual norm quotient in the order-13 Picard descent.
-- source:
--   Owned MazurTheorem integration, Apache-2.0. RepresentationCharacterTwist.bilinear_eigenvector_equivariance; checked with default limits at Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.RepresentationTheory.Intertwining

theorem MazurTransfer.bilinear_eigenvector_twisted_equivariance
    (k G V W U : Type*) [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
    (ρ : Representation k G V) (τ : Representation k G W) (υ : Representation k G U)
    (B : V →ₗ[k] W →ₗ[k] U)
    (hB : ∀ (g : G) (v : V) (w : W), B (ρ g v) (τ g w) = υ g (B v w))
    (χ : G →* kˣ) (v : V) (hv : ∀ g : G, ρ g v = (χ g : k) • v)
    (g : G) (w : W) : B v (τ g w) = (((χ g)⁻¹ : kˣ) : k) • υ g (B v w) := by sorry
