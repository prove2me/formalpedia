-- Prove2me | Theorems.Thm_OAI_Erdos3_jointAffineBoolean_regularization_error_s2
-- name    : OAI.Erdos3.jointAffineBoolean_regularization_error_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:48:12.495986+00:00
-- url     : https://prove2.me/theorems/78de323a-94ae-48f5-9bc2-3a3483f83d73
-- title:
--   Smoothing the image of the joint affine Boolean sampler at width ρ changes test integrals by at most 2η plus a translation budget times ρ
-- statement:
--   Let $D$ and $\alpha$ be finite types with decidable equality, and for each $d \in D$ let $B_d$ and $O_d$ be finite types with decidable equality and $h_d$ a natural number. Write $\mathrm{BP}_d$ = `BlockParameter (B d) (Fin (h d)) α` $= B_d \times \operatorname{Fin} h_d \times \operatorname{Option} \alpha$ (defined by OpenAI), and $\mathrm{JBP}$ for the disjoint union $\Sigma_d\, \mathrm{BP}_d$ (`JointBlockParameter`). (All named objects are defined by OpenAI.) Let:
--   - $c_d : B_d \to \mathbb{R}$; $\mathrm{sets}_d : O_d \to \operatorname{Finset} \alpha$ with $\#\mathrm{sets}_d(o) \le h_d$; $\mathrm{block}_d : O_d \to B_d$ injective; $v_d \in \operatorname{Fin} h_d$; $\mathrm{sel}_d : O_d \to \operatorname{Option} \alpha$;
--   - $L_d$ a continuous linear automorphism of $\mathrm{BP}_d \to \mathbb{R}$ and $b_d \in (\mathrm{BP}_d \to \mathbb{R})$, and $\delta : D \to \mathbb{R}$ with $0 < \delta_d \le 1$, such that $\|L_d\| \le 1$, $\delta_d \|L_d^{-1}\| \le 1$, and $b_d + L_d x$ has all coordinates in $[-1, 1]$ whenever $x$ does;
--   - $C : D \to \mathbb{R}$ with $C_d \ge 0$ and $|c_d(\mathrm{block}_d(o))| \le C_d$ for all $d, o$;
--   - $\psi : \mathbb{R} \to \mathbb{R}$ smooth ($C^\infty$) with values in $[0, 1]$ and $\psi(t) = 0$ for $|t| \le 1$; $A, T \ge 0$ with $\psi$ $A$-Lipschitz and Mathlib's `Real.smoothTransition` $T$-Lipschitz;
--   - $r_d : B_d \times \operatorname{Fin} h_d \to \mathbb{R}$ positive; $\kappa : D \to \mathbb{R}$ positive; $K, H \ge 0$ with $\delta_d^{-1} \cdot$ `productMinorInverseBound (#O_d) (#α) (h d) (C d) 1 (κ d)` $\le K$ and `productMinorDerivativeBound (#BP_d) (#O_d) (#α) (h d) (C d) 1` $\le H$ for all $d$ (explicit real expressions of OpenAI);
--   - $\eta$ a real number with $1 - \eta \le \int$ `jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ` $(x)\, dx$ (Lebesgue measure on $\mathrm{JBP} \to \mathbb{R}$; the integrand is OpenAI's product over $d$ of affine Boolean cube good weights);
--   - $\rho > 0$ a nonnegative real, and $\varphi$ a measurable real function on $(\Sigma_d O_d) \to \mathbb{R}$ with $|\varphi(x)| \le 1$ for all $x$.
--
--   Let $\beta$ = `jointBooleanSource h`, OpenAI's product over $d$ of the block cube measures on $\mathrm{BP}_d \to \mathbb{R}$, and let $\Phi$ = `jointAffineBooleanSampler c sets L b`, the map sending $x \in \mathrm{JBP} \to \mathbb{R}$ to the family over $d$ of `booleanSamplerMap (c d) (sets d) (b d + L d x_d)` (a vector indexed by $O_d$). Then
--   $$\Bigl| \int \texttt{regularizedImageDensity}\ \beta\ \Phi\ \rho\ (y)\, \varphi(y)\, dy - \int \varphi(\Phi(x))\, d\beta(x) \Bigr| \le 2\eta + \texttt{jointAffineBooleanTranslationBudget C A T r κ K H} \cdot \rho,$$
--   where the first integral is against Lebesgue measure on $(\Sigma_d O_d) \to \mathbb{R}$, `regularizedImageDensity β Φ ρ` is the mixture over $x \sim \beta$ of the densities $y \mapsto \prod_o \rho^{-1} \psi_0((y_o - \Phi(x)_o)/\rho)$ with $\psi_0$ OpenAI's smooth probability profile, the second integral is `mappedTest β Φ φ`, and `jointAffineBooleanTranslationBudget` is an explicit nonnegative real defined by OpenAI.
--
--   Lean: `OAI.Erdos3.jointAffineBoolean_regularization_error_s2`, which states OpenAI's `OAI.Erdos3.jointAffineBoolean_regularization_error` (in `lean/OAI/Combinatorics/Progressions/Lattices/JointAffineBooleanSource.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B078`, `OAIE3v2B100` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/JointAffineBooleanSource.lean (declaration OAI.Erdos3.jointAffineBoolean_regularization_error)

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

theorem jointAffineBoolean_regularization_error_s2
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
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) (K H : ℝ≥0)
    (hK : ∀ d, (δ d)⁻¹ * productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
      (h d) (C d) 1 (κ d) ≤ K)
    (hH : ∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ H)
    {η : ℝ}
    (hmass : 1 - η ≤ ∫ x, jointAffineBooleanGoodWeight c sets block v sel
      (fun d => (L d).toContinuousLinearMap) b ψ r κ x)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (φ : ((Σ d, O d) → ℝ) → ℝ)
    (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x, regularizedImageDensity (jointBooleanSource h)
        (jointAffineBooleanSampler c sets L b) ρ x * φ x) -
      mappedTest (jointBooleanSource h) (jointAffineBooleanSampler c sets L b) φ| ≤
      2 * η + jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H * ρ := by
  sorry

end Erdos3

end

end OAI
end
