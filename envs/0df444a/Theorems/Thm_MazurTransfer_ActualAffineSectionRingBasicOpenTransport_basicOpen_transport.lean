-- Prove2me | Theorems.Thm_MazurTransfer_ActualAffineSectionRingBasicOpenTransport_basicOpen_transport
-- name    : MazurTransfer.ActualAffineSectionRingBasicOpenTransport.basicOpen_transport
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T04:55:28.224833+00:00
-- url     : https://prove2.me/theorems/4aa96f31-7d28-44af-b5ec-c4b22ca16b07
-- title:
--   Transporting basic opens through an actual affine-open comparison
-- statement:
--   Let $X$ be a scheme, let $U$ be an open subset, let $B$ be a commutative ring, and let $e:\operatorname{Spec}B\xrightarrow{\sim}U$ be a specified isomorphism. For $b\in B$, let $\widetilde b\in\Gamma(X,U)$ be its inverse image under the specified global-section comparison. Then $$D_X(\widetilde b)=(\iota_U\circ e)\bigl(D_{\operatorname{Spec}B}(b)\bigr).$$ This gives the precise basic-open identity required by the actual order-thirteen finite-map parameters.
-- source:
--   Unchanged original statement and proof body from checked MazurTheorem ActualAffineSectionRingBasicOpenTransport.lean. Complete Lean frontend declaration and command ranges hoist the solution and its section binders. The complete original kernel type is checked by a closed witness. The exact public formal type and its direct imports are checked locally. Original per-file headers, Apache-2.0 and the actual order-thirteen downstream consumer are retained. Vas and contributors.

import Mathlib
import Definitions.Def_MazurTransfer_ActualAffineSectionRingTransport
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open MazurTransfer.ActualAffineSectionRingBasicOpenTransport

theorem MazurTransfer.ActualAffineSectionRingBasicOpenTransport.basicOpen_transport {X : Scheme.{u}} (U : X.Opens) {B : Type u} [CommRing B]  (e : Spec (.of B) ≅ U.toScheme) (b : B) :
    X.basicOpen (transportedSection U e b) =
      (e.hom ≫ U.ι) ''ᵁ PrimeSpectrum.basicOpen b  := by sorry
