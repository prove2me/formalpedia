-- Prove2me | Theorems.Thm_OAI_Erdos3_affineCoefficientImage_enormous_error_s2
-- name    : OAI.Erdos3.affineCoefficientImage_enormous_error_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:40:13.26723+00:00
-- url     : https://prove2.me/theorems/db33e4fe-e392-473f-90e6-8cfcd574d580
-- title:
--   Under fiber control and a large scale H, the integer image law of an affine coefficient profile is close to its selected-column density mask
-- statement:
--   Let $I, J$ be finite types with decidable equality, $A$ an integer matrix with rows indexed by $I$ and columns by $J$, $s : I \hookrightarrow J$ an embedding (selected columns), and $S : J \to \mathbb{R}$ with $S(j) > 0$ for all $j$. Let $H, L, C, U, G$ be reals and $h$ a natural number such that `CoefficientFiberControl A s S H L h C U G` holds (a proposition defined by OpenAI: the square submatrix of $A$ on the columns $s$ has nonzero determinant; $H/L^h \le S(j)$ for all $j$; $|A_{i, s(j)}| \le C L^h$; the entries of OpenAI's normalized integer column matrix are at most $C$ in absolute value; the inverse of OpenAI's normalized pivot matrix has sup-operator norm at most $U$; and the index of the image lattice $A\mathbb{Z}^J$ in $\mathbb{Z}^I$ is at most $G$). Assume $L > 0$, $H > 0$, $C \ge 0$. Let $c, w : J \to \mathbb{R}$ with $w(j) > 0$, let $\delta > 0$ be a nonnegative real with $\delta \le w(j)$ for all $j$, and let $R \ge 0$ with $|c(j)| + w(j) \le R$ for all $j$. Let $f$ = `affineProductProfile c w`, i.e. $f(x) = \prod_j w(j)^{-1} \psi((x_j - c(j))/w(j))$ with $\psi$ OpenAI's smooth probability profile (a smooth bump with integral $1$). Write $a = \#I$, $u$ for the number of unselected columns $\#\{j \in J : j \notin \operatorname{range} s\}$, and $K$ = `affineProductProfileLip J δ` $= \#J \cdot \texttt{probabilityProfileLipschitz} \cdot \delta^{-(\#J + 1)}$. Assume
--   $$2\bigl(1 + (2R + 2)^{a + u} K\bigr) \cdot (a!\, C^a) \cdot L^{h(a+1)} \le H.$$
--   Then the total weight $Z = \sum_{z \in \mathbb{Z}^J} f(z_j/S(j))_j$ (`coefficientWeightSum f S`) is positive, and for every $v \in \mathbb{Z}^I$,
--   $$\Bigl| H^a \cdot \Pr[A z = v] - \texttt{coefficientImageMask A (fun _ => H) φ}\ v \Bigr| \le \frac{\texttt{normalizedFiberErrorConstant}\ a\ u\ G\ U\ (uC)\ R\ (\delta^{-1})^{\#J}\ K \cdot (a!\, C^a) \cdot L^{h(a+1)}}{H},$$
--   where $z \in \mathbb{Z}^J$ is drawn with probability proportional to $f(z_j / S(j))_j$ (so $\Pr[Az = v]$ is the probability of $v$ under `coefficientImagePMF A f _ S hS _ hZ`); $\varphi$ = `selectedCoefficientDensity A s _ S (fun _ => H) hS _ f` is OpenAI's normalized fiber density for the pivot columns $s$; `coefficientImageMask A P φ v` equals the index of $A\mathbb{Z}^J$ in $\mathbb{Z}^I$ times $\varphi(v_i/P_i)_i$ if $v \in A\mathbb{Z}^J$ and $0$ otherwise; and `normalizedFiberErrorConstant` is an explicit real constant of OpenAI.
--
--   Lean: `OAI.Erdos3.affineCoefficientImage_enormous_error_s2`, which states OpenAI's `OAI.Erdos3.affineCoefficientImage_enormous_error` (in `lean/OAI/Combinatorics/Progressions/Lattices/IntegerRowInterpolationMixture.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B100` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/IntegerRowInterpolationMixture.lean (declaration OAI.Erdos3.affineCoefficientImage_enormous_error)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B100

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem affineCoefficientImage_enormous_error_s2 {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {H L C U G : ℝ} (h : ℕ) (ctrl : CoefficientFiberControl A s S H L h C U G)
    (hL : 0 < L) (hH : 0 < H) (hC : 0 ≤ C)
    (c w : J → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w j) {R : ℝ} (hR : 0 ≤ R) (hsupport : ∀ j, |c j| + w j ≤ R)
    (hlarge : 2 * (1 + (2 * R + 2) ^ (Fintype.card I + Fintype.card (UnselectedColumn s)) *
      affineProductProfileLip J δ) * ((Fintype.card I).factorial * C ^ Fintype.card I) *
      L ^ (h * (Fintype.card I + 1)) ≤ H) :
    ∃ hZ : 0 < coefficientWeightSum (affineProductProfile c w) S, ∀ v,
      |H ^ Fintype.card I *
        (coefficientImagePMF A (affineProductProfile c w) (affineProductProfile_nonneg c w hw)
          S hS (affineProductProfile_zero_outside c w hw hR hsupport) hZ v).toReal -
        coefficientImageMask A (fun _ => H)
          (selectedCoefficientDensity A s ctrl.det_ne_zero S (fun _ => H) hS (fun _ => hH)
            (affineProductProfile c w)) v| ≤
      (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card (UnselectedColumn s))
        G U (Fintype.card (UnselectedColumn s) * C) R ((δ : ℝ)⁻¹ ^ Fintype.card J)
        (affineProductProfileLip J δ) * ((Fintype.card I).factorial * C ^ Fintype.card I)) *
          L ^ (h * (Fintype.card I + 1)) / H := by
  sorry

end Erdos3

end

end OAI
end
