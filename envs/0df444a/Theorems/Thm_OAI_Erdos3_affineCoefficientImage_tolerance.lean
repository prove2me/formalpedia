-- Prove2me | Theorems.Thm_OAI_Erdos3_affineCoefficientImage_tolerance
-- name    : OAI.Erdos3.affineCoefficientImage_tolerance
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T11:23:17.856306+00:00
-- url     : https://prove2.me/theorems/f9d21848-3812-498b-b09d-069e9f40b023
-- title:
--   Local law for the integer image of an affine product profile under fiber control
-- statement:
--   Let $I,J$ be finite types with decidable equality, $A\in\mathbb Z^{I\times J}$, $s\colon I\hookrightarrow J$, $S\colon J\to\mathbb R$ with $S_j>0$, reals $H,L,C,U,G$, $h\in\mathbb N$, and assume `CoefficientFiberControl A s S H L h C U G`: a structure (a proposition) bundling that the selected minor $(A_{i,s(i')})$ has nonzero determinant, $H/L^h\le S_j$ for all $j$, $|A_{i,s(j)}|\le CL^h$, every entry $A_{ij}S_j/H$ of `normalizedIntegerColumns A S (fun _ => H)` has absolute value at most $C$, the inverse of the normalized selected minor $(A_{i,s(i')}S_{s(i')}/H)$ has sup operator norm at most $U$, and the index of the column-span lattice of $A$ in $\mathbb Z^I$ is at most $G$. Assume $L>0$, $H>0$, $C,U,G\ge0$. Let $c,w\colon J\to\mathbb R$ with $w_j>0$, $\delta>0$ (a nonnegative real) with $\delta\le w_j$, $R\ge0$ with $|c_j|+w_j\le R$ for all $j$, and reals $b,t,\varepsilon$ with $b\ge0$, $t\ge0$, $\varepsilon>0$, $G,U,C,R\le e^b$ and $\delta^{-1}\le e^t$. Assume
--   $$\exp\big(\Lambda\big)\,(1+\varepsilon^{-1})\,L^{h(|I|+1)}\le H,\qquad\Lambda=\texttt{coefficientLogAllowance}\ |I|\ d\ (\texttt{affineCoefficientCommonBudget}\ |J|\ d\ b\ t),$$
--   where $d$ is the number of unselected columns $j\notin s(I)$ (`UnselectedColumn s`), `coefficientLogAllowance j d β` $=2j^2+(2j+4)\beta+(j+2d)(\beta+4)+4$ and `affineCoefficientCommonBudget n d b t` $=b+d+$ `affineProfileLogBound n t`. Let $f=$ `affineProductProfile c w`, the function $x\mapsto\prod_jw_j^{-1}\phi((x_j-c_j)/w_j)$ on $\mathbb R^J$ ($\phi=$ `smoothProbabilityProfile`). Then there is a proof `hZ` that $0<$ `coefficientWeightSum f S` $=\sum_{z\in\mathbb Z^J}f(z/S)$, such that for every $v\in\mathbb Z^I$,
--   $$\big|H^{|I|}\,\pi(v)-\texttt{coefficientImageMask}\ A\ \bar H\ g\ v\big|\le\varepsilon,$$
--   where $\bar H$ is the constant scale $H$ on $I$, $\pi=$ `coefficientImagePMF A f … hZ` is the law of $Az$ when $z\in\mathbb Z^J$ has probability proportional to $f(z/S)$ (coordinatewise division); `coefficientImageMask A P g v` is the index of the column-span lattice of $A$ times $g(v/P)$ if $v$ lies in that lattice and $0$ otherwise; and $g=$ `selectedCoefficientDensity A s _ S (fun _ => H) … f`, a real function on $\mathbb R^I$ (a `normalizedFiberDensity` built from the selected minor, the remaining columns and the scales).
--
--   Lean: `OAI.Erdos3.affineCoefficientImage_tolerance` in `lean/OAI/Combinatorics/Progressions/Lattices/ResidueCoefficientFamily.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B014` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/ResidueCoefficientFamily.lean#L65

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem affineCoefficientImage_tolerance {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {H L C U G : ℝ} (h : ℕ) (ctrl : CoefficientFiberControl A s S H L h C U G)
    (hL : 0 < L) (hH : 0 < H) (hC0 : 0 ≤ C) (hU0 : 0 ≤ U) (hG0 : 0 ≤ G)
    (c w : J → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w j) {R : ℝ} (hR0 : 0 ≤ R) (hsupport : ∀ j, |c j| + w j ≤ R)
    {b t ε : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (hε : 0 < ε)
    (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b) (hC : C ≤ Real.exp b) (hR : R ≤ Real.exp b)
    (hi : (δ : ℝ)⁻¹ ≤ Real.exp t)
    (hlarge : Real.exp (coefficientLogAllowance (Fintype.card I) (Fintype.card (UnselectedColumn s))
        (affineCoefficientCommonBudget (Fintype.card J) (Fintype.card (UnselectedColumn s)) b t)) *
      (1+ε⁻¹) * L^(h*(Fintype.card I+1)) ≤ H) :
    ∃ hZ : 0 < coefficientWeightSum (affineProductProfile c w) S, ∀ v,
      |H ^ Fintype.card I *
        (coefficientImagePMF A (affineProductProfile c w) (affineProductProfile_nonneg c w hw)
          S hS (affineProductProfile_zero_outside c w hw hR0 hsupport) hZ v).toReal -
        coefficientImageMask A (fun _ => H)
          (selectedCoefficientDensity A s ctrl.det_ne_zero S (fun _ => H) hS (fun _ => hH)
            (affineProductProfile c w)) v| ≤ ε := by
  sorry

end Erdos3
end
end OAI
