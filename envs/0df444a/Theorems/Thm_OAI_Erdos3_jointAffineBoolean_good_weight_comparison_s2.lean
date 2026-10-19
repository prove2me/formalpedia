-- Prove2me | Theorems.Thm_OAI_Erdos3_jointAffineBoolean_good_weight_comparison_s2
-- name    : OAI.Erdos3.jointAffineBoolean_good_weight_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:41:13.907076+00:00
-- url     : https://prove2.me/theorems/df95b77a-1fd3-4205-99c3-87b14d68c6d6
-- title:
--   A map C2-close to the joint affine Boolean sampler has nearly the same image averages, given a large good weight
-- statement:
--   Let $D$ and $\alpha$ be finite types with decidable equality. For $d \in D$ let $B_d$, $O_d$ be finite types with decidable equality and $h_d$ a natural number; write `BlockParameter (B d) (Fin (h d)) α` $= B_d \times \operatorname{Fin} h_d \times \mathrm{Option}\ \alpha$ and `JointBlockParameter B h α` for the disjoint union over $d$ of these types.
--
--   Let the data be:
--   - $c_d : B_d \to \mathbb{R}$; `sets d` $: O_d \to$ finite subsets of $\alpha$ with $|\texttt{sets}_d(o)| \le h_d$; injective maps `block d` $: O_d \to B_d$; $v_d \in \operatorname{Fin} h_d$; `sel d` $: O_d \to \mathrm{Option}\ \alpha$;
--   - continuous linear automorphisms $L_d$ of the space of real functions on `BlockParameter (B d) (Fin (h d)) α`, and such functions $b_d$;
--   - reals $\delta_d$ with $0 < \delta_d \le 1$, $\lVert L_d \rVert \le 1$, $\delta_d \lVert L_d^{-1} \rVert \le 1$, and: whenever $|x(z)| \le 1$ for all $z$, also $|(b_d + L_d x)(z)| \le 1$ for all $z$;
--   - reals $C_d \ge 0$ with $|c_d(\texttt{block}_d(o))| \le C_d$ for all $o$;
--   - $\psi : \mathbb{R} \to \mathbb{R}$ infinitely differentiable with values in $[0, 1]$ and $\psi(t) = 0$ for $|t| \le 1$; $A, T \in \mathbb{R}_{\ge 0}$ with $\psi$ $A$-Lipschitz and Mathlib's `Real.smoothTransition` $T$-Lipschitz;
--   - $r_d : B_d \times \operatorname{Fin} h_d \to \mathbb{R}$ with all values positive; $\kappa_d > 0$;
--   - $K, H_0 \in \mathbb{R}_{\ge 0}$ with $\delta_d^{-1} \cdot$ `productMinorInverseBound |O d| |α| (h d) (C d) 1 (κ d)` $\le K$ and `productMinorDerivativeBound |BlockParameter (B d) (Fin (h d)) α| |O d| |α| (h d) (C d) 1` $\le H_0$ for all $d$ (explicit bounds defined by OpenAI);
--   - $V$, a $C^2$ map from real functions on `JointBlockParameter B h α` to real functions on $\Sigma_d O_d$;
--   - reals $\varepsilon, \eta$ with $0 < \varepsilon \le 1$ and $K\varepsilon \le 1/2$;
--   - (hmass) $1 - \eta \le \int$ `jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ` $(x)\, dx$ (Lebesgue measure; OpenAI's weight: for each $d$, the affine Boolean cube good weight of block $d$, combined over $d$);
--   - (herr) for every $x$ with $|x(z)| \le 1$ for all $z$: $\lVert V(x) - \Sigma(x) \rVert \le \varepsilon$, $\lVert DV(x) - D\Sigma(x) \rVert \le \varepsilon$ and $\lVert D^2 V(x) - D^2\Sigma(x) \rVert \le \varepsilon$, where $\Sigma$ = `jointAffineBooleanSampler c sets L b` (OpenAI's map applying, on each block $d$, the Boolean sampler map of $c_d$ and `sets d` to $b_d + L_d x$) and $D$ denotes the Fréchet derivative;
--   - $\varphi$, a measurable real function on real functions on $\Sigma_d O_d$ with $|\varphi(y)| \le 1$ for all $y$.
--
--   Let $S$ = `jointBooleanWeightBudget h C A T r κ` (an explicit real number defined by OpenAI) and
--   $$Q = 1 + 2KS + |\texttt{JointBlockParameter B h alpha}| \cdot (2K)^2 (H_0 + 1).$$
--   Then, with $\nu$ = `jointBooleanSource h` (OpenAI's product of the block cube probability measures) and `mappedTest ν U φ` $= \int \varphi(U(a))\, d\nu(a)$,
--   $$\bigl| \texttt{mappedTest}(\nu, \Sigma, \varphi) - \texttt{mappedTest}(\nu, V, \varphi) \bigr| \le 2\eta + 4\,\Bigl|\Sigma_d O_d\Bigr| \sqrt{Q \varepsilon}.$$
--
--   Lean: `OAI.Erdos3.jointAffineBoolean_good_weight_comparison_s2`, which states OpenAI's `OAI.Erdos3.jointAffineBoolean_good_weight_comparison` (in `lean/OAI/Combinatorics/Progressions/Lattices/JointAffineBooleanSource.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B078`, `OAIE3v2B100` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/JointAffineBooleanSource.lean (declaration OAI.Erdos3.jointAffineBoolean_good_weight_comparison)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B078
import Definitions.Def_OAIE3v2B100

section

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}

theorem jointAffineBoolean_good_weight_comparison_s2
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (hblock : ∀ d, Function.Injective (block d))
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) ≃L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ))
    (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (δ : D → ℝ) (hδ : ∀ d, 0 < δ d) (hδone : ∀ d, δ d ≤ 1)
    (hL : ∀ d, ‖(L d).toContinuousLinearMap‖ ≤ 1)
    (hLinv : ∀ d, δ d * ‖(L d).symm.toContinuousLinearMap‖ ≤ 1)
    (hbox : ∀ d x, (∀ z, |x z| ≤ 1) → ∀ z, |(b d + L d x) z| ≤ 1)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) (K H₀ : ℝ≥0)
    (hK : ∀ d, (δ d)⁻¹ * productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
      (h d) (C d) 1 (κ d) ≤ K)
    (hH : ∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ H₀)
    (V : (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ)) (hV : ContDiff ℝ 2 V)
    {ε η : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) (hsmall : (K : ℝ) * ε ≤ 1 / 2)
    (hmass : 1 - η ≤ ∫ x, jointAffineBooleanGoodWeight c sets block v sel
      (fun d => (L d).toContinuousLinearMap) b ψ r κ x)
    (herr : ∀ x, (∀ z, |x z| ≤ 1) →
      ‖V x - jointAffineBooleanSampler c sets L b x‖ ≤ ε ∧
      ‖fderiv ℝ V x - fderiv ℝ (jointAffineBooleanSampler c sets L b) x‖ ≤ ε ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ (jointAffineBooleanSampler c sets L b)) x‖ ≤ ε)
    (φ : ((Σ d, O d) → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ y, ‖φ y‖ ≤ 1) :
    let S := jointBooleanWeightBudget (O := O) (α := α) h C A T r κ
    let Q := 1 + 2 * (K : ℝ) * S +
      (Fintype.card (JointBlockParameter B h α) : ℝ) * ((2 * (K : ℝ)) ^ 2 * ((H₀ : ℝ) + 1))
    |mappedTest (jointBooleanSource h) (jointAffineBooleanSampler c sets L b) φ -
      mappedTest (jointBooleanSource h) V φ| ≤
      2 * η + 4 * (Fintype.card (Σ d, O d) : ℝ) * Real.sqrt (Q * ε) := by
  sorry

end Erdos3

end

end OAI
end
