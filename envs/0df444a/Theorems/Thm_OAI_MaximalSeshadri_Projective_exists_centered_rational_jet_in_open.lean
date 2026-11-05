-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Projective_exists_centered_rational_jet_in_open
-- name    : OAI.MaximalSeshadri.Projective.exists_centered_rational_jet_in_open
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:32.318911+00:00
-- url     : https://prove2.me/theorems/ee5dc642-ec61-4e37-bb23-e8f570a2caa9
-- title:
--   A centered étale chart with a rational jet
-- statement:
--   Let $K$ be an algebraically closed field, $X$ integral, smooth of relative dimension 2 over $K$, with sections $s$ giving a closed immersion over $K$. Let $p$ be a point outside `centeredOpen s`, and $W$ an open containing $p$. There is an affine open $U$ with $p\in U\subset W$ inside the iso-open of $s_{\mathrm{none}}$, indices $i:\operatorname{Fin}2\to\sigma$, a $K$-point $\rho$ of $\Gamma(U)$ killing all section ratios, and a jet map $\tau$ to the 3-jets in two variables with kernel $(\ker\rho)^3$, sending the ratios of $s_{i_j}$ to minus the coordinates, with those ratios giving étale coordinates, and with the scalar structures compatible.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionsMorphism k s hs` is the morphism from $X$ to $\operatorname{Proj}$ of the graded polynomial ring in variables indexed by the sections, defined by sections whose iso-opens cover $X$, with $k$ the ring map from the base into $\Gamma(X,\top)$. `centeredOpen s` is the union of the iso-opens of $s_{\mathrm{some}\,i}$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Projective.exists_centered_rational_jet_in_open`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/FramedNodalChart.lean#L78

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [IsAlgClosed K] [Fintype σ] {X : Scheme} {M : X.Modules}

theorem exists_centered_rational_jet_in_open [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)]
    (hbase : sectionsMorphism k s hs ≫ projectiveToSpec = g)
    (p : X) (hp : p ∉ centeredOpen s) (W : X.Opens) (hpW : p ∈ W) :
    ∃ U : X.affineOpens, p ∈ U.1 ∧ U.1 ≤ W ∧
      ∃ hU : U.1 ≤ SectionOpens.isoOpen (s none),
        let _ : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra
        ∃ i : Fin 2 → σ, ∃ ρ : Γ(X, U.1) →ₐ[K] K,
          ∃ τ : Γ(X, U.1) →ₐ[K] JetAlgebra (Fin 2) K 3,
            (∀ j : σ, ρ (affineSectionRatios s U hU (some j)) = 0) ∧
            RingHom.ker τ = (RingHom.ker ρ)^3 ∧
            (∀ f, jetAugment 3 (by decide) (τ f) = ρ f) ∧
            (∀ j : Fin 2, τ (affineSectionRatios s U hU (some (i j))) =
              -Ideal.Quotient.mk _ (MvPolynomial.X j)) ∧
            (MvPolynomial.eval₂Hom (openScalars g U.1)
              (fun j => -affineSectionRatios s U hU (some (i j)))).Etale ∧
            ∀ c : K, U.1.topIso.hom (U.1.ι.appTop (k c)) = openScalars g U.1 c := by
  sorry

end
end MaximalSeshadri.Projective
end
end OAI
