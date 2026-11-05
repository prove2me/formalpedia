-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_divide_by_power_section
-- name    : OAI.MaximalSeshadri.Geometry.divide_by_power_section
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:10:08.985806+00:00
-- url     : https://prove2.me/theorems/f3f59acd-19cc-41be-868b-4704aaa86d57
-- title:
--   Division by a section of a power
-- statement:
--   Let $X$ be integral over $\mathbb C$, $L$ a line bundle, $a$ sections of $L^d$ with iso-opens covering $X$, $v$ with nonzero combination $\omega$, and $t$ a section of $L^{d+n}$ whose pullback to the section ideal's subscheme vanishes. Then there is a unique section $q$ of $L^n$ with $q\cdot\omega=t$ under `linePowerAdd`.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionIdeal k s hs v` is the comap along `sectionsMorphism` of the ideal sheaf of the hyperplane with coefficients $v$; `sectionCombination k s v` is $\sum_j k(v_j)s_j$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.divide_by_power_section`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/TensorDivision.lean#L166

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}

theorem divide_by_power_section [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) (d n : ℕ)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(X,⊤))
    (a : σ → (O X ⟶ (L.pow d).sheaf))
    (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    (v : σ → ℂ) (hne : sectionCombination k a v ≠ 0)
    (t : O X ⟶ (L.pow (d+n)).sheaf)
    (ht : pullbackSection (sectionIdeal k a ha v).subschemeι t = 0) :
    ∃! q : O X ⟶ (L.pow n).sheaf,
      q ≫ sectionMultiply (L.pow d) (L.pow n) (sectionCombination k a v) ≫
        (linePowerAdd L d n).inv = t := by
  sorry

end
end MaximalSeshadri.Geometry
end
end
end
end OAI
