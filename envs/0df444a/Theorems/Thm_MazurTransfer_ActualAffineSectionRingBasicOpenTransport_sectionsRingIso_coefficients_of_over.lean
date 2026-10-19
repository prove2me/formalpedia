-- Prove2me | Theorems.Thm_MazurTransfer_ActualAffineSectionRingBasicOpenTransport_sectionsRingIso_coefficients_of_over
-- name    : MazurTransfer.ActualAffineSectionRingBasicOpenTransport.sectionsRingIso_coefficients_of_over
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T05:47:51.987706+00:00
-- url     : https://prove2.me/theorems/1bc561b7-9d3e-4223-a506-91db4423543d
-- title:
--   An affine-open section-ring comparison preserves structural coefficients
-- statement:
--   Let $R$ be a commutative ring, let $c:X\to\operatorname{Spec}R$ be a scheme morphism, let $U$ be an open subset of $X$, and let $B$ be an $R$-algebra. Suppose $e:\operatorname{Spec}B\xrightarrow{\sim}U$ is compatible with the structure maps to $\operatorname{Spec}R$. Then the specified comparison $E:\Gamma(X,U)\xrightarrow{\sim}B$ preserves coefficients: $$E(c^*r)=\operatorname{algebraMap}_{R,B}(r)\qquad(r\in R).$$ This supplies the coefficient identity used to turn the two actual finite-chart section-ring comparisons into $R$-algebra isomorphisms.
-- source:
--   Generalization of the original structural coefficient-comparison arguments in MazurTheorem Order13SingleSectionComplementCoefficientCompatibility.lean and Order13InverseParameterCurveCoefficientCompatibility.lean. The direct proof retains the specified base-compatibility identity, the actual open inclusion, and the canonical global-sections maps for spectra. It imports the already published affine-open section-ring constructor interface. Native, strict and full frontend checks pass with standard axioms only; the exact public formal type is kernel-compared with the checked solution. Apache-2.0. Named downstream consumers are both actual finite-chart R-algebra section comparisons in FiniteMapData. Vas and contributors.

import Mathlib
import Definitions.Def_MazurTransfer_ActualAffineSectionRingTransport
open CategoryTheory AlgebraicGeometry Opposite
open MazurTransfer.ActualAffineSectionRingBasicOpenTransport
universe u

theorem MazurTransfer.ActualAffineSectionRingBasicOpenTransport.sectionsRingIso_coefficients_of_over (R : Type u) [CommRing R] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of R)) (U : X.Opens) (B : Type u) [CommRing B] [Algebra R B]
    (e : Spec (.of B) ≅ U.toScheme)
    (he : e.hom ≫ U.ι ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    (Scheme.ΓSpecIso (.of R)).inv ≫
      c.appLE ⊤ U (by intro x hx; exact trivial) ≫ (sectionsRingIso U e).hom =
      CommRingCat.ofHom (algebraMap R B)  := by sorry
