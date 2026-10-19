-- Prove2me | Theorems.Thm_OAI_Erdos3_affineCoefficientImage_residue_tolerance_s2
-- name    : OAI.Erdos3.affineCoefficientImage_residue_tolerance_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:39:01.840682+00:00
-- url     : https://prove2.me/theorems/dc295661-7ef4-4040-b644-3baa979b053d
-- title:
--   Local limit with residue multiplier for the image of an affine coefficient profile under an integer matrix
-- statement:
--   Let $I$, $J$, $N$ be finite types with decidable equality. Let $A$ be an $I \times J$ integer matrix and $s : I \hookrightarrow J$ an embedding such that the square submatrix of $A$ with columns $s$ has nonzero determinant; let $C$ be an $I \times N$ integer matrix. Let $S : J \to \mathbb{R}$ and $T : N \to \mathbb{R}$ be positive. Let $H, L, B, U, G$ be reals and $h$ a natural number such that `CoefficientFiberControl (fromCols A C) (inl ∘ s) (Sum.elim S T) H L h B U G` holds (an OpenAI-defined property of the block matrix $[A \mid C]$ with pivot columns $s$ and column scales $S \sqcup T$: nonzero pivot determinant, $H/L^h \le$ every scale, integer and normalized entry bounds by $B L^h$ and $B$, inverse bound $U$ for the normalized pivot, and further bounds involving $G$). Assume $L > 0$, $H > 0$, $B \ge 0$, $U \ge 0$, $G \ge 0$.
--
--   Let $c, w : J \sqcup N \to \mathbb{R}$ with $w > 0$; let $\delta \in \mathbb{R}_{\ge 0}$ with $\delta > 0$ and $\delta \le w(j)$ for all $j$; let $R \in \mathbb{R}_{\ge 0}$ with $\lvert c(j)\rvert + w(j) \le R$ for all $j$. Let $b, t, \varepsilon$ be reals with $b \ge 0$, $t \ge 0$, $\varepsilon > 0$, $G, U, B, R \le e^{b}$ and $\delta^{-1} \le e^{t}$, and assume `coefficientReplacementScale (inl ∘ s) b t ε L h` $\le H$ (an explicit OpenAI scale). Let $m$ be a natural number and $r$ an $I \times N$ matrix over $\mathbb{Z}/m$ such that the lattice $m\mathbb{Z}^I$ (`integerScalarLattice I m`) is contained in the image $A\mathbb{Z}^J$, and $r$ is the reduction of $C$ modulo $m$.
--
--   Then the total weight `coefficientWeightSum (affineProductProfile c w) (Sum.elim S T)` $= \sum_{z \in \mathbb{Z}^{J \sqcup N}} f(z/(S \sqcup T))$ is positive, where $f$ = `affineProductProfile c w` is the product over coordinates of OpenAI's smooth bump profiles centered at $c$ with widths $w$; and for every $v \in \mathbb{Z}^I$,
--   $$\Bigl\lvert H^{\lvert I\rvert} \cdot \Pr\bigl[[A \mid C] z = v\bigr] - \texttt{coefficientResidueMultiplier}(A, r, v) \cdot \texttt{kernelCoefficientDensity}(A, s, S, H, C, T, c, w)\bigl(v/H\bigr)\Bigr\rvert \le \varepsilon,$$
--   where $z \in \mathbb{Z}^{J \sqcup N}$ is drawn with probability proportional to $f(z/(S \sqcup T))$ (this probability is `coefficientImagePMF (fromCols A C) (affineProductProfile c w) … v` as a real number), `coefficientResidueMultiplier A r v` is OpenAI's lattice multiplier for $[A \mid \tilde r]$ at $v$ (with $\tilde r$ a lift of $r$), `kernelCoefficientDensity` is OpenAI's limiting density (with all heights equal to $H$), and $v/H$ denotes $(v_i/H)_i$.
--
--   Lean: `OAI.Erdos3.affineCoefficientImage_residue_tolerance_s2`, which states OpenAI's `OAI.Erdos3.affineCoefficientImage_residue_tolerance` (in `lean/OAI/Combinatorics/Progressions/Lattices/ResidueCoefficientFamily.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B100` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/ResidueCoefficientFamily.lean (declaration OAI.Erdos3.affineCoefficientImage_residue_tolerance)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B100

section

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem affineCoefficientImage_residue_tolerance_s2 {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0) (C : Matrix I N ℤ)
    (S : J → ℝ) (T : N → ℝ) (hS : ∀ j, 0 < S j) (hT : ∀ n, 0 < T n)
    {H L B U G : ℝ} (h : ℕ)
    (ctrl : CoefficientFiberControl (Matrix.fromCols A C) (s.trans Function.Embedding.inl)
      (Sum.elim S T) H L h B U G)
    (hL : 0 < L) (hH : 0 < H) (hB0 : 0 ≤ B) (hU0 : 0 ≤ U) (hG0 : 0 ≤ G)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R)
    {b t ε : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (hε : 0 < ε)
    (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b) (hB : B ≤ Real.exp b) (hR : (R : ℝ) ≤ Real.exp b)
    (hi : (δ : ℝ)⁻¹ ≤ Real.exp t)
    (hlarge : coefficientReplacementScale (J := J ⊕ N) (s.trans Function.Embedding.inl) b t ε L h ≤ H)
    (m : ℕ) (r : Matrix I N (ZMod m))
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range) (hr : integerResidueMatrix C m = r) :
    ∃ hZ : 0 < coefficientWeightSum (affineProductProfile c w) (Sum.elim S T), ∀ v,
      |H ^ Fintype.card I *
        (coefficientImagePMF (Matrix.fromCols A C) (affineProductProfile c w)
          (affineProductProfile_nonneg c w hw) (Sum.elim S T) (Sum.rec hS hT)
          (affineProductProfile_zero_outside c w hw R.coe_nonneg hsupport) hZ v).toReal -
        coefficientResidueMultiplier A r v *
          kernelCoefficientDensity A s hA S (fun _ => H) hS (fun _ => hH) C T c w
            (fun i => (v i : ℝ)/H)| ≤ ε := by
  sorry

end Erdos3

end

end OAI
end
