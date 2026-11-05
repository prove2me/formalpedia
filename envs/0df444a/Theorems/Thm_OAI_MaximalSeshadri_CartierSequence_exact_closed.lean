-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_CartierSequence_exact_closed
-- name    : OAI.MaximalSeshadri.CartierSequence.exact_closed
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:07:50.215348+00:00
-- url     : https://prove2.me/theorems/8feb0fc8-fbb8-48d0-a6ff-8ef3df24ac37
-- title:
--   The Cartier sequence for a closed immersion
-- statement:
--   Let $f:Y\to X$ be a closed immersion, $M,N$ line bundles on $X$, $\varphi:M\to N$ a monomorphism whose coefficient locally generates the kernel ideal of $f$ on affine frames. Then $0\to M\to N\to f_*f^*N\to0$ is short exact.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.CartierSequence.exact_closed`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/ArbitraryCartierEuler.lean#L44

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.CartierSequence
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

theorem exact_closed {Y : Scheme.{0}} (f : Y ⟶ X) [IsClosedImmersion f]
    (M N : LineBundle X) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
        (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        f.ker.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))}) :
    ∃ hz : φ ≫ LineClosedUnit.map f N = 0,
      (ShortComplex.mk φ (LineClosedUnit.map f N) hz).ShortExact := by
  sorry

end
end MaximalSeshadri.CartierSequence
end
end OAI
