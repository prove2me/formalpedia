-- Prove2me | Theorems.Thm_OAI_Erdos3_normalizedIntegerImage_polynomial_error_s2
-- name    : OAI.Erdos3.normalizedIntegerImage_polynomial_error_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:32:06.873439+00:00
-- url     : https://prove2.me/theorems/4b2aa15e-5fd3-4269-b791-f3c0ff171870
-- title:
--   Polynomial error bound for the local limit of the integer image law against the masked normalized fiber density
-- statement:
--   Let $I$ and $J$ be finite types with decidable equality. Let $A$ be an $I \times I$ integer matrix with $\det A \ne 0$ and $B$ an $I \times J$ integer matrix. Let $S, P : I \to \mathbb{R}$ and $T : J \to \mathbb{R}$ be positive. Let $f : \mathbb{R}^J \times \mathbb{R}^I \to \mathbb{R}$ be nonnegative and $K$-Lipschitz for some $K \in \mathbb{R}_{\ge 0}$. Let $R, G, U, V, C, L, \rho, H$ be reals and $h$ a natural number with $R \ge 0$, $\rho > 0$, $H \ge 0$, and assume:
--   - $\rho \le S(i)$ for all $i$, $\rho \le T(j)$ for all $j$, and $\lvert\det A\rvert \le \rho$;
--   - $\lvert A_{ij}\rvert \le C L^h$ for all $i, j$;
--   - $f(p) = 0$ whenever $\lVert p\rVert > R$, and $\int f = 1$ (Lebesgue measure);
--   - $(2R + 2)^{\lvert I\rvert + \lvert J\rvert} \cdot K \cdot \lvert\det A\rvert/\rho \le 1/2$;
--   - $\lVert f(p)\rVert \le H$ for all $p$;
--   - the index of the lattice `pivotFullImage A B` $= A\mathbb{Z}^I + B\mathbb{Z}^J$ in $\mathbb{Z}^I$ is at most $G$;
--   - the operator norm of the inverse of `normalizedPivotEquiv A hA S P hS hP` (OpenAI: $A$ rescaled by the input scales $S$ and output scales $P$) is at most $U$;
--   - the operator norm (for the sup norm) of `normalizedIntegerColumns B T P` ($B$ rescaled by $T$ and $P$) is at most $V$.
--
--   Then the scaled input mass `scaledInputMass f S T` is positive, and for every $v \in \mathbb{Z}^I$,
--   $$\Bigl\lvert \Bigl(\prod_i P(i)\Bigr) \Pr[A x + B y = v] - \texttt{maskedIntegerImageDensity A B P}(\phi)(v)\Bigr\rvert \le \frac{\texttt{normalizedFiberErrorConstant}(\lvert I\rvert, \lvert J\rvert, G, U, V, R, H, K) \cdot \lvert I\rvert!\, C^{\lvert I\rvert} \cdot L^{h\lvert I\rvert}}{\rho},$$
--   where $(y, x) \in \mathbb{Z}^J \times \mathbb{Z}^I$ is drawn with probability proportional to $f(y/T, x/S)$ (this probability is `integerImagePMF A B f … v` as a real number), $\phi$ = `normalizedFiberDensity A hA B S P T hS hP f` is OpenAI's normalized fiber density on $\mathbb{R}^I$, `maskedIntegerImageDensity A B P φ v` equals the index of `pivotFullImage A B` times $\phi(v/P)$ if $v$ lies in that lattice and $0$ otherwise, and `normalizedFiberErrorConstant` is an explicit constant defined by OpenAI.
--
--   Lean: `OAI.Erdos3.normalizedIntegerImage_polynomial_error_s2`, which states OpenAI's `OAI.Erdos3.normalizedIntegerImage_polynomial_error` (in `lean/OAI/Combinatorics/Progressions/Estimates/NormalizedImageMask.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B085` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/NormalizedImageMask.lean (declaration OAI.Erdos3.normalizedIntegerImage_polynomial_error)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B085

section

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

theorem normalizedIntegerImage_polynomial_error_s2 {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 < T j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R G U V C L ρ H : ℝ} (h : ℕ) (hR : 0 ≤ R) (hρ : 0 < ρ) (hH : 0 ≤ H)
    (hscaleS : ∀ i, ρ ≤ S i) (hscaleT : ∀ j, ρ ≤ T j) (hsmall : (A.det.natAbs : ℝ) ≤ ρ)
    (hcoeff : ∀ i j, |(A i j : ℝ)| ≤ C * L ^ h)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hmass : (∫ p, f p) = 1)
    (hsmallMass : (2 * R + 2) ^ (Fintype.card I + Fintype.card J) * K *
      ((A.det.natAbs : ℝ) / ρ) ≤ 1 / 2)
    (hbound : ∀ p, ‖f p‖ ≤ H)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap‖ ≤ U)
    (hcol : ‖matrixSupCLM (normalizedIntegerColumns B T P)‖ ≤ V) :
    ∃ hM : 0 < scaledInputMass f S T, ∀ v,
      |(∏ i, P i) * (integerImagePMF A B f hf0 S T hS hT hsupport hM v).toReal -
        maskedIntegerImageDensity A B P (normalizedFiberDensity A hA B S P T hS hP f) v| ≤
      (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card J) G U V R H K *
        ((Fintype.card I).factorial * C ^ Fintype.card I)) * L ^ (h * Fintype.card I) / ρ := by
  sorry

end Erdos3

end

end OAI
end
