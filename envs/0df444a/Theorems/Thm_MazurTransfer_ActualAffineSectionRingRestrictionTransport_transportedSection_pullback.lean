-- Prove2me | Theorems.Thm_MazurTransfer_ActualAffineSectionRingRestrictionTransport_transportedSection_pullback
-- name    : MazurTransfer.ActualAffineSectionRingRestrictionTransport.transportedSection_pullback
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T04:55:42.137469+00:00
-- url     : https://prove2.me/theorems/47c039eb-900f-4183-96e4-3c1091be209a
-- title:
--   A transported affine section restricts to its literal ring image
-- statement:
--   Let $X$ be a scheme, $U$ an open subset, $e:\operatorname{Spec}B\xrightarrow{\sim}U$ a specified affine presentation, and $\varphi:B\to A$ a homomorphism of commutative rings. Let $b\in B$ and let $\widetilde b\in\Gamma(X,U)$ be its transported section. For the morphism $j=\iota_U\circ e\circ\operatorname{Spec}\varphi$, with the specified factorization through $U$, the restriction of $\widetilde b$ to $\operatorname{Spec}A$, read through its canonical global-sections isomorphism, is $$j^*(\widetilde b)=\varphi(b).$$ This is the restriction identity used for the product of the actual order-thirteen reciprocal parameters.
-- source:
--   Unchanged original statement and proof body from checked MazurTheorem ActualAffineSectionRingRestrictionTransport.lean. Complete Lean frontend declaration and command ranges hoist the solution and its section binders. The complete original kernel type is checked by a closed witness. The exact public formal type and its direct imports are checked locally. Original per-file headers, Apache-2.0 and the actual order-thirteen downstream consumer are retained. Vas and contributors.

import Mathlib
import Definitions.Def_MazurTransfer_ActualAffineSectionRingTransport
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open MazurTransfer.ActualAffineSectionRingBasicOpenTransport

theorem MazurTransfer.ActualAffineSectionRingRestrictionTransport.transportedSection_pullback {X : Scheme.{u}} (U : X.Opens) {B A : Type u} [CommRing B] [CommRing A]  (e : Spec (.of B) ≅ U.toScheme)
    (φ : B →+* A) (b : B)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ e.hom ≫ U.ι) ⁻¹ᵁ U) :
    (Scheme.ΓSpecIso (.of A)).hom
      ((Spec.map (CommRingCat.ofHom φ) ≫ e.hom ≫ U.ι).appLE U ⊤ h
        (transportedSection U e b)) = φ b  := by sorry
