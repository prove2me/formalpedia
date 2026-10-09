-- Prove2me | Theorems.Thm_OAI_Erdos3_affineCoefficientImage_residue_family
-- name    : OAI.Erdos3.affineCoefficientImage_residue_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:25:46.765699+00:00
-- url     : https://prove2.me/theorems/bd523c89-fb82-48af-a94a-03d5c83a0588
-- title:
--   Uniform local law for a family of coefficient images sharing residues mod m
-- statement:
--   Let $\Omega$ be a finite type with `FiniteProbabilityWeights` $p$, and $I,J,N$ finite types with decidable equality. Let $A\in\mathbb Z^{I\times J}$ and $s\colon I\hookrightarrow J$ with $\det(A_{i,s(i')})\ne0$, $C\colon\Omega\to\mathbb Z^{I\times N}$, $S\colon J\to\mathbb R$, $T\colon N\to\mathbb R$ positive, reals $H,L,B,U,G$ and $h\in\mathbb N$. Assume that for every $\omega$ with $p(\omega)\ne0$, `CoefficientFiberControl [A | C ω] s' (S ⊔ T) H L h B U G` holds, where $[A\,|\,C_\omega]\in\mathbb Z^{I\times(J\oplus N)}$ is `Matrix.fromCols`, $s'$ is $s$ followed by the left inclusion $J\hookrightarrow J\oplus N$, and $S\sqcup T$ is the combined scale; this structure (a proposition) bundles that the selected minor has nonzero determinant, $H/L^h\le$ every scale, the selected entries are at most $BL^h$ in absolute value, every normalized entry (entry times scale over $H$) is at most $B$, the inverse of the normalized selected minor has sup operator norm at most $U$, and the index of the column-span lattice is at most $G$. Assume $L>0$, $H>0$, $B,U,G\ge0$. Let $c,w\colon J\oplus N\to\mathbb R$ with $w>0$, $\delta>0$ with $\delta\le w$ everywhere, $R\ge0$ with $|c_j|+w_j\le R$, reals $b,t,\varepsilon$ with $b,t\ge0$, $\varepsilon>0$, $G,U,B,R\le e^b$, $\delta^{-1}\le e^t$, and `coefficientReplacementScale s' b t ε L h` $\le H$, where `coefficientReplacementScale s b t ε L h` is $\exp(\texttt{coefficientLogAllowance}\ |I|\ d\ (\texttt{affineCoefficientCommonBudget}\ |J\oplus N|\ d\ b\ t))\,(1+\varepsilon^{-1})\,L^{h(|I|+1)}$ with $d$ the number of unselected columns. Let $m\in\mathbb N$ and $r\in(\mathbb Z/m)^{I\times N}$, with $m\mathbb Z^I$ contained in the column span of $A$, and $C_\omega\equiv r\pmod m$ entrywise whenever $p(\omega)\ne0$. Let $f=$ `affineProductProfile c w` $=\prod_jw_j^{-1}\phi((x_j-c_j)/w_j)$ ($\phi=$ `smoothProbabilityProfile`). Then there is a proof `hZ` that $0<$ `coefficientWeightSum f (S ⊔ T)` $=\sum_zf(z/(S\sqcup T))$, such that $0\le\mu(v)\le G$ for every $v\in\mathbb Z^I$, where $\mu(v)=$ `coefficientResidueMultiplier A r v` is the index of the column-span lattice of $[A\,|\,\tilde r]$ if $v$ lies in it and $0$ otherwise ($\tilde r=$ `liftResidueMatrix r`, an integer lift of $r$); and for every $\omega$ with $p(\omega)\ne0$ and every $v\in\mathbb Z^I$,
--   $$\big|H^{|I|}\,\pi_\omega(v)-\mu(v)\cdot\texttt{kernelCoefficientDensity}\ A\ s\ \_\ S\ \bar H\ \ldots\ C_\omega\ T\ c\ w\ (v/H)\big|\le\varepsilon,$$
--   where $\bar H$ is the constant scale $H$ on $I$, $v/H$ is coordinatewise, $\pi_\omega=$ `coefficientImagePMF [A | C ω] f … hZ` is the law of $[A\,|\,C_\omega]z$ when $z\in\mathbb Z^{J\oplus N}$ has probability proportional to $f(z/(S\sqcup T))$, and `kernelCoefficientDensity` is a real function on $\mathbb R^I$ built from the selected minor of $A$, the remaining columns of $A$, the columns of $C_\omega$, the scales and the profile $(c,w)$.
--
--   Lean: `OAI.Erdos3.affineCoefficientImage_residue_family` in `lean/OAI/Combinatorics/Progressions/Lattices/ResidueCoefficientFamily.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B014` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/ResidueCoefficientFamily.lean#L274

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

namespace OAI

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem affineCoefficientImage_residue_family {Ω I J N : Type*} [Fintype Ω]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (p : FiniteProbabilityWeights Ω)
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0) (C : Ω → Matrix I N ℤ)
    (S : J → ℝ) (T : N → ℝ) (hS : ∀ j, 0 < S j) (hT : ∀ n, 0 < T n)
    {H L B U G : ℝ} (h : ℕ)
    (ctrl : ∀ ω, p.weight ω ≠ 0 → CoefficientFiberControl (Matrix.fromCols A (C ω))
      (s.trans Function.Embedding.inl) (Sum.elim S T) H L h B U G)
    (hL : 0 < L) (hH : 0 < H) (hB0 : 0 ≤ B) (hU0 : 0 ≤ U) (hG0 : 0 ≤ G)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R)
    {b t ε : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (hε : 0 < ε)
    (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b) (hB : B ≤ Real.exp b) (hR : (R : ℝ) ≤ Real.exp b)
    (hi : (δ : ℝ)⁻¹ ≤ Real.exp t)
    (hlarge : coefficientReplacementScale (J := J ⊕ N) (s.trans Function.Embedding.inl) b t ε L h ≤ H)
    (m : ℕ) (r : Matrix I N (ZMod m))
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range)
    (hr : ∀ ω, p.weight ω ≠ 0 → integerResidueMatrix (C ω) m = r) :
    ∃ hZ : 0 < coefficientWeightSum (affineProductProfile c w) (Sum.elim S T),
      (∀ v, 0 ≤ coefficientResidueMultiplier A r v ∧ coefficientResidueMultiplier A r v ≤ G) ∧
      ∀ ω, p.weight ω ≠ 0 → ∀ v,
        |H ^ Fintype.card I *
          (coefficientImagePMF (Matrix.fromCols A (C ω)) (affineProductProfile c w)
            (affineProductProfile_nonneg c w hw) (Sum.elim S T) (Sum.rec hS hT)
            (affineProductProfile_zero_outside c w hw R.coe_nonneg hsupport) hZ v).toReal -
          coefficientResidueMultiplier A r v *
            kernelCoefficientDensity A s hA S (fun _ => H) hS (fun _ => hH)
              (C ω) T c w (fun i => (v i : ℝ)/H)| ≤ ε := by
  sorry

end Erdos3
end
end OAI
