-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Interpolation_eventual_germ_jet_test
-- name    : OAI.MaximalSeshadri.Interpolation.eventual_germ_jet_test
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:09:12.042343+00:00
-- url     : https://prove2.me/theorems/97e1b38a-35a1-4162-bdb6-521a001526ba
-- title:
--   An eventual jet test for spaces of convergent germs
-- statement:
--   Let $d,H>0$, $T>1$ with $d^2Ht<(1+t)^2$ for $t>T$. Let $V_k$ be finite-dimensional spaces of convergent power series coefficients such that for $k>0$, $t>T$, every initial exponent of $V_k$ for weight $t$ lies in the quadrilateral with vertices $(0,0)$, $(kdHt/(1+t),0)$, $(k/d,k/d)$, $(0,kdH/(1+t))$. Then there is $r_0>0$ such that for $r\ge r_0$ and $k,m>0$ with $k\sqrt{H/r}<m$, there is $R>0$ with all series in $V_k$ having derivative-summable majorants on radius $R$, and for each $\varepsilon>0$ there are $r$ distinct points in the polydisc of radius $\min(\varepsilon,R)$ at which the $m$-jet evaluation is injective on $V_k$.
--
--   **Notation.** `nodeQuadrilateral a b c` is the convex hull of $(0,0),(a,0),(c,c),(0,b)$. `LexInitial c t e` says that $c_e\ne0$ and $e$ minimizes $p_1+tp_2$ among exponents with nonzero coefficient, ties broken by the smaller second coordinate.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Interpolation.eventual_germ_jet_test`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/GermInterpolation.lean#L132

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
open scoped BigOperators Topology
open Filter Set

theorem eventual_germ_jet_test (d H T : ℝ) (hd : 0 < d) (hH : 0 < H) (hT : 1 < T)
    (hweight : ∀ t : ℝ, T < t → d ^ 2 * H * t < (1 + t) ^ 2)
    (V : ℕ → Submodule ℂ (Exponent → ℂ))
    [∀ k, FiniteDimensional ℂ (V k)]
    (hconv : ∀ k c, c ∈ V k → ConvergentSeries c)
    (hbound : ∀ k, 0 < k → ∀ t, T < t → ∀ e ∈ initialExponentSet (V k) t,
      ((e.1 : ℝ), (e.2 : ℝ)) ∈ nodeQuadrilateral
        ((k : ℝ) * (d * H * t / (1 + t)))
        ((k : ℝ) * (d * H / (1 + t))) ((k : ℝ) / d)) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      ∀ k m : ℕ, 0 < k → 0 < m → (k : ℝ) * Real.sqrt (H / r) < (m : ℝ) →
      ∃ R : ℝ, 0 < R ∧ (∀ c ∈ V k, DerivativeSummable c R) ∧
        ∀ ε : ℝ, 0 < ε → ∃ q : Fin r → ℂ × ℂ, Function.Injective q ∧
          (∀ j, ‖(q j).1‖ < min ε R ∧ ‖(q j).2‖ < min ε R) ∧
          Function.Injective (fun f : V k => finiteJetColumn r m q (seriesEval f)) := by
  sorry

end MaximalSeshadri.Interpolation
end
end OAI
