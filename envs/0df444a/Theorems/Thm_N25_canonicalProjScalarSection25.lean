-- Prove2me | Theorems.Thm_N25_canonicalProjScalarSection25
-- name    : N25.canonicalProjScalarSection25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:31:46.444199+00:00
-- url     : https://prove2.me/theorems/dfbdbd94-2892-4794-970d-d7797176c74a
-- title:
--   The scalar section on every basic Proj open agrees with the structure morphism
-- statement:
--   Let $K$ be a field, let $R=\bigoplus_{n≥0}R_n$ be the canonical cone ring, and let $f∈R_m$ be homogeneous of positive degree $m>0$. On the basic open $D_+(f)⊆\operatorname{Proj}(R)$, let $λ_f:K→(R_f)_0$ be the scalar map into the degree-zero localization and let $s_f:\operatorname{Spec}((R_f)_0)→D_+(f)$ be the canonical Proj chart section. Then $$s_f∘\operatorname{Spec}(λ_f)=π|_{D_+(f)},$$ after the standard identification $\operatorname{Spec}(K)≅\operatorname{Spec}(R_0)$. This compatibility lets the local chart morphisms glue to the global structure map. Formalization note: the displayed equality includes the library’s canonical global-section isomorphism and restriction maps.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
import Definitions.Def_N25_CanonicalPrincipalOpenChart

universe u
open N25
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
variable (K : Type u) [Field K]

theorem N25.canonicalProjScalarSection25 (f : CanonicalConeRing25 K) {m : ℕ}
    (hf : f ∈ canonicalConePiece25 K m) (hm : 0 < m) :
    CommRingCat.ofHom ((fromZeroRingHom (canonicalConePiece25 K) (Submonoid.powers f)).comp
      (algebraMap K (canonicalConePiece25 K 0))) ≫
        Proj.awayToSection (canonicalConePiece25 K) f =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (canonicalProjectiveCurveToSpec25 K).appLE ⊤ (Proj.basicOpen (canonicalConePiece25 K) f) le_top := by sorry
