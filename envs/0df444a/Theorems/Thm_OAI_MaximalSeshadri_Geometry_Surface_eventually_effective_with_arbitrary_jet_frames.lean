-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_eventually_effective_with_arbitrary_jet_frames
-- name    : OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_arbitrary_jet_frames
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:07:44.669415+00:00
-- url     : https://prove2.me/theorems/a45d50db-b418-41a4-bd25-750c04ff9b5a
-- title:
--   Effective sections with prescribed vanishing
-- statement:
--   Let $L$ be ample on $S$ and $M$ a line bundle with $L\cdot M\ge0$. Let $m_i$ be natural numbers with $\sum_im_i^2<M^2$, and for each $i$ let $U_i$ be an affine open with étale coordinates and a $\mathbb C$-point $\rho_i$. Then there is $N>0$ such that for $n\ge N$ and any frames $e_i$ of $M^n$ on $U_i$, there is a nonzero section $s$ of $M^n$ with coefficient in $(\ker\rho_i)^{nm_i}$ for all $i$.
--
--   **Notation.** $L^2$ is `selfIntersection`, namely $\chi(L^2)-2\chi(L)+\chi(\mathcal O_S)$. $L\cdot M$ is `mixedEuler`, namely $\chi(L\otimes M)-\chi(L)-\chi(M)+\chi(\mathcal O_S)$. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_arbitrary_jet_frames`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Jets/EffectiveJetFrames.lean#L19

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem Surface.eventually_effective_with_arbitrary_jet_frames (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme)
    (hm : 0 ≤ mixedEuler S L M) {r : ℕ} (m : Fin r → ℕ)
    (hq : (∑ i, (m i)^2 : ℕ) < selfIntersection S M)
    (U : Fin r → S.scheme.affineOpens)
    (t : ∀ i, Fin 2 → Γ(S.scheme,(U i).1))
    (het : ∀ i, (MvPolynomial.eval₂Hom (openScalars S.structureMap (U i).1) (t i)).Etale)
    (ρ : ∀ i, letI := (openScalars S.structureMap (U i).1).toAlgebra;
      Γ(S.scheme,(U i).1) →ₐ[ℂ] ℂ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ e : ∀ i, (M.pow n).sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme,
      ∃ s : O S.scheme ⟶ (M.pow n).sheaf, s ≠ 0 ∧
        ∀ i, affineCoefficient (U i) (e i) s ∈
          (RingHom.ker (ρ i))^(n*m i) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
