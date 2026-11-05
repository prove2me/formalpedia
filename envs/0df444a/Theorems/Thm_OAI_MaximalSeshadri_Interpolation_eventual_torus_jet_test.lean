-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Interpolation_eventual_torus_jet_test
-- name    : OAI.MaximalSeshadri.Interpolation.eventual_torus_jet_test
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T15:18:14.155501+00:00
-- url     : https://prove2.me/theorems/5e2df2ba-1761-4dfe-b377-68e9e47c93e8
-- title:
--   An eventual jet test for Laurent polynomials on a triangle
-- statement:
--   Let $d,H>0$, $T>1$. There is $r_0>0$ such that for $r\ge r_0$ there are $t>T$ and $r$ distinct points of $(\mathbb C^*)^2$ with the following property. If $k,m>0$ with $k\sqrt{H/r}<m$, and $s$ is a nonempty finite set of exponents in the scaled `compressedTriangle` $k\cdot\operatorname{conv}\{(-dH/(1+t),0),(dHt/(1+t),0),(0,1/d)\}$ with nonzero coefficients $c$, then the Laurent polynomial with exponents $s$ and coefficients $c$ has a mixed $m$-jet which is nonzero at some point.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Interpolation.eventual_torus_jet_test`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/TorusJets.lean#L158

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise

theorem eventual_torus_jet_test (d H T : ℝ) (hd : 0 < d) (hH : 0 < H) (hT : 1 < T) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      ∃ t : ℝ, T < t ∧ ∃ points : Fin r → ℂ × ℂ,
        Function.Injective points ∧ (∀ l, (points l).1 ≠ 0 ∧ (points l).2 ≠ 0) ∧
        ∀ (k m : ℕ), 0 < k → 0 < m → (k : ℝ) * Real.sqrt (H / r) < (m : ℝ) →
          ∀ (s : Finset (ℤ × ℤ)), s.Nonempty →
            (∀ p ∈ s, ((p.1 : ℝ), (p.2 : ℝ)) ∈ (k : ℝ) • compressedTriangle d H t) →
            ∀ c : ℤ × ℤ → ℂ, (∀ p ∈ s, c p ≠ 0) →
              ∃ l : Fin r, ¬ MixedJetZero (laurentEval s c) (points l).1 (points l).2 m := by
  sorry

end MaximalSeshadri.Interpolation
end
end OAI
