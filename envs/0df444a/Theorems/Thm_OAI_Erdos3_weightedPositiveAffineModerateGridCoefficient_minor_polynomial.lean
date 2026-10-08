-- Prove2me | Theorems.Thm_OAI_Erdos3_weightedPositiveAffineModerateGridCoefficient_minor_polynomial
-- name    : OAI.Erdos3.weightedPositiveAffineModerateGridCoefficient_minor_polynomial
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T11:15:01.008445+00:00
-- url     : https://prove2.me/theorems/0837e045-0d10-4e38-9594-4bb7ad2a34d7
-- title:
--   Weighted positive affine grid coefficients are small off a polynomial major-arc cover
-- statement:
--   Let $n\in\mathbb N$ and $I$ a finite type with decidable equality. Let $c$ be a `NormalizedScalarCubeSource Empty` and $s_j$ ($j\in\mathrm{Fin}(n+1)$) a `NormalizedScalarCubeSource I` (structures bundling a length $\ell>0$, a modulus bound, moduli $m_i>0$ and residues, and a bounded Lipschitz weight, normalized so that it determines a probability law `source` on an integer scalar cube box). Let $A\ge0$ with `Real.smoothTransition` $A$-Lipschitz, and reals $U,V,\zeta$. Assume `ScalarCubePrimitiveBudget c A U` and `ScalarCubePrimitiveBudget (s j) A U` for all $j$ (a predicate bounding $|I|+1$, the modulus bound, the weight bound, the weight's Lipschitz constant and two boundary constants by $U$). Let $u_j\colon\mathrm{Option}\,I\to\mathbb R$ and $v_j\colon\mathrm{Option}\,I\to\mathbb N$ with $v_j(i)>0$ and $v_j(i)\,m_i(s_j)\le U$ for all $j,i$. Assume (`hpositive`) $\ell(c)/4\le z(\mathrm{none})$ for every $z$ of nonzero weight under `c.source`; $0\le V$; $0<\zeta\le1$; $\ell(s_j)\ge$ `positiveModerateLengthConstant n U` $/\zeta^{\texttt{positiveModerateLengthExponent}\ n}$ for all $j$; $M\in\mathbb N$ with $M>0$ and $M/(\ell(c)\prod_j\ell(s_j))\le V$; and a finite family $J$ of finite subsets of $I$, each of size at most $n+1$. Then for every frequency $k\colon J\to\mathrm{Fin}\,M$ outside `polynomialGridCover J M (positiveModerateCoverConstant n |J| U V) (positiveModerateCoverExponent n |J|) ζ`,
--   $$\big|\texttt{weightedAffineModerateGridCoefficient}\ c\ s\ u\ v\ 0\ M\ J\ k\big|\le\zeta .$$
--   Here `weightedAffineModerateGridCoefficient c s u v 0 M J k` is the complex mean, under `c.source` (variable $z$) and then the product of the laws `(s j).source` (variable $x$), of the unit-circle character evaluated at $z(\mathrm{none})$ times `booleanBlockPhase` of the frequencies $S\mapsto k_S/M$ ($S\in J$, $0$ off $J$) against the affine coordinates $i\mapsto u_j(i)+v_j(i)\,x_j(i)$; `polynomialGridCover J M C r ζ` is the finite set `rationalGridMajorBox J M Q Q` with $Q=\lceil C/\zeta^r\rceil$, the product over $J$ of the sets `rationalGridMajorSet M Q Q` of residues mod $M$; and the length and cover constants and exponents are OpenAI's explicit numerical parameters.
--
--   Lean: `OAI.Erdos3.weightedPositiveAffineModerateGridCoefficient_minor_polynomial` in `lean/OAI/Combinatorics/Progressions/Fourier/UniformSpectrumAbsoluteCap.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B012` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Fourier/UniformSpectrumAbsoluteCap.lean#L441

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B012

namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedPositiveAffineModerateGridCoefficient_minor_polynomial {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (c : NormalizedScalarCubeSource Empty)
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V ζ : ℝ}
    (hc : ScalarCubePrimitiveBudget c A U) (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (hstride : ∀ j i, ((v j i * (s j).modulus i : ℕ) : ℝ) ≤ U)
    (hpositive : ∀ z, c.source.weight z ≠ 0 → (c.length : ℝ) / 4 ≤ (z none : ℝ))
    (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : ∀ j, positiveModerateLengthConstant n U / ζ ^ positiveModerateLengthExponent n ≤
      (s j).length)
    {M : ℕ} (hM : 0 < M)
    (hscale : (M : ℝ) / ((c.length : ℝ) * ∏ j, ((s j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (k : J → Fin M) (hk : k ∉ polynomialGridCover J M (positiveModerateCoverConstant n J.card U V)
      (positiveModerateCoverExponent n J.card) ζ) :
    ‖weightedAffineModerateGridCoefficient c s u v 0 M J k‖ ≤ ζ := by
  sorry

end Erdos3
end
end OAI
