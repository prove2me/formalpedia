-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_maximal_cartier_extraction_of_iso
-- name    : OAI.MaximalSeshadri.Geometry.maximal_cartier_extraction_of_iso
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:04:16.223213+00:00
-- url     : https://prove2.me/theorems/7c7bd6b5-9aba-4d2c-8866-b152b88cdc21
-- title:
--   Extracting the maximal power of an integral divisor from a section
-- statement:
--   Let $X$ be integral and proper over $\mathbb C$, $M\cong L^d$ with $d>0$, $s$ a finite family of sections of $M$ with iso-opens covering $X$ and nonzero combination, with integral zero subscheme, and $U$ an affine open meeting the zero subscheme, on which $L$ and $M$ are trivial and the coefficient $g$ of the combination is a non-unit. If $t\ne0$ is a section of $L^a$ with trivialization on $U$, then there are $j,n$ with $a=jd+n$ and a nonzero section $q$ of $L^n$ which does not vanish on the zero subscheme, such that $g^j\cdot(\text{coefficient of }q)$ is associated to the coefficient of $t$.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionIdeal k s hs v` is the comap along `sectionsMorphism` of the ideal sheaf of the hyperplane with coefficients $v$; `sectionCombination k s v` is $\sum_j k(v_j)s_j$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.maximal_cartier_extraction_of_iso`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/MaximalCartierIso.lean#L19

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}} [IsIntegral X]

theorem maximal_cartier_extraction_of_iso (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L M : LineBundle X) (d : ℕ) (hd : 0 < d) (E : M.sheaf ≅ (L.pow d).sheaf)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(X,⊤))
    (s : σ → (O X ⟶ M.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (U : X.affineOpens) [Nonempty U.1]
    [Nonempty ((sectionIdeal k s hs v).subschemeι ⁻¹ᵁ U.1).toScheme]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (eM : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hnu : ¬ IsUnit (affineCoefficient U eM (sectionCombination k s v)))
    (a : ℕ) (t : O X ⟶ (L.pow a).sheaf) (ht : t ≠ 0)
    (eA : (L.pow a).sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    ∃ j n : ℕ, a = j*d+n ∧ ∃ q : O X ⟶ (L.pow n).sheaf, q ≠ 0 ∧
      pullbackSection (sectionIdeal k s hs v).subschemeι q ≠ 0 ∧
      Associated ((affineCoefficient U eM (sectionCombination k s v))^j *
        affineCoefficient U (localPowerFrame U.1 e n) q) (affineCoefficient U eA t) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
