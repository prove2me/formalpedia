-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_power_extension_ratio
-- name    : OAI.MaximalSeshadri.Geometry.LineBundle.power_extension_ratio
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:07:36.803979+00:00
-- url     : https://prove2.me/theorems/c330bd01-d6ea-4035-abe8-71abb3cb393a
-- title:
--   Extending a ratio by a power of a section
-- statement:
--   Let $X$ be integral and compact, $L$ a line bundle, $s$ a section with nonempty nonvanishing open $D$, and $f$ a function on $D$. There is $N$ such that for $n\ge N$ there is a section $t$ of $L^n$ with $t|_D=f\cdot s^n|_D$.
--
--   **Notation.** `sectionOpen X s` is the same union for a global section $s$: its nonvanishing open.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.LineBundle.power_extension_ratio`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/FramedMaps.lean#L176

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ ι : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
  (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
  (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
  (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1)

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ ι κ : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames MaximalSeshadri.Projective
variable {X : Scheme}

theorem LineBundle.power_extension_ratio [IsIntegral X] [CompactSpace X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (f : Γ((sectionOpen X s).toScheme, ⊤)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : GlobalSections X (modulePow X L.sheaf n),
      restrictSection (sectionOpen X s).ι t = scalarEnd f ≫
        restrictSection (sectionOpen X s).ι (powerSection s n) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end
end
end OAI
