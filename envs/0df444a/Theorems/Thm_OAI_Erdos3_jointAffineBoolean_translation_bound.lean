-- Prove2me | Theorems.Thm_OAI_Erdos3_jointAffineBoolean_translation_bound
-- name    : OAI.Erdos3.jointAffineBoolean_translation_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T23:44:19.703623+00:00
-- url     : https://prove2.me/theorems/d1d08c5a-56e8-4e74-b164-af3ced231cb4
-- title:
--   Translation bound for the cut-off joint affine Boolean sampler
-- statement:
--   Let $D$, $\alpha$ be finite types with decidable equality, for each $d \in D$ let $B_d$, $O_d$ be finite types with decidable equality, and let $h : D \to \mathbb{N}$ (these are section variables). Write $P_d = B_d \times \mathrm{Fin}(h_d) \times \mathrm{Option}\ \alpha$ (`BlockParameter`) and $\Pi = \Sigma_d P_d$ (`JointBlockParameter B h α`). Let $c : \forall d, B_d \to \mathbb{R}$, $\mathrm{sets}_d : O_d \to \mathrm{Finset}\ \alpha$, and $\mathrm{block}_d : O_d \to B_d$ injective for each $d$; let $v : \forall d, \mathrm{Fin}(h_d)$ and $\mathrm{sel} : \forall d, O_d \to \mathrm{Option}\ \alpha$, with $|\mathrm{sets}_d(o)| \le h_d$ for all $d, o$. Let $L_d$ be continuous linear automorphisms of $\mathbb{R}^{P_d}$ and $b_d \in \mathbb{R}^{P_d}$, and let $\delta : D \to \mathbb{R}$ with $0 < \delta_d \le 1$, $\|L_d\| \le 1$, $\delta_d \|L_d^{-1}\| \le 1$, and such that $|x_z| \le 1$ for all $z$ implies $|(b_d + L_d x)_z| \le 1$ for all $z$. Let $C : D \to \mathbb{R}$ with $C_d \ge 0$ and $|c_d(\mathrm{block}_d(o))| \le C_d$ for all $d, o$. Let $\psi : \mathbb{R} \to \mathbb{R}$ be $C^\infty$ with values in $[0,1]$ and $\psi(t) = 0$ for $|t| \le 1$, and let $A, T \in \mathbb{R}_{\ge 0}$ with $\psi$ $A$-Lipschitz and Mathlib's `Real.smoothTransition` $T$-Lipschitz. Let $r : \forall d, B_d \times \mathrm{Fin}(h_d) \to \mathbb{R}$ with all values positive, $\kappa : D \to \mathbb{R}$ with all values positive, and $K, H \in \mathbb{R}_{\ge 0}$ with $\delta_d^{-1}\cdot$ `productMinorInverseBound` $(|O_d|, |\alpha|, h_d, C_d, 1, \kappa_d) \le K$ and `productMinorDerivativeBound` $(|P_d|, |O_d|, |\alpha|, h_d, C_d, 1) \le H$ for every $d$ (both explicit real-valued functions of OpenAI). Then `ImageTranslationBound μ U Λ` holds, where $\mu$ is the measure with density `jointAffineBooleanCutoff c sets block v sel L b ψ r κ` (OpenAI's product of per-block cutoff weights on $\mathbb{R}^\Pi$) with respect to `jointBooleanSource h` (OpenAI's product measure on $\mathbb{R}^\Pi$), $U$ = `jointAffineBooleanSampler c sets L b` $: \mathbb{R}^\Pi \to \mathbb{R}^{\Sigma_d O_d}$, and $\Lambda$ = `jointAffineBooleanTranslationBudget C A T r κ K H` $\in \mathbb{R}_{\ge 0}$ (an explicit constant of OpenAI). Here `ImageTranslationBound μ U Λ` means: for every measurable $\varphi : \mathbb{R}^{\Sigma_d O_d} \to \mathbb{R}$ with $|\varphi| \le 1$ and every $z$,
--   $$\Bigl|\int \varphi(U(a) + z)\,d\mu(a) - \int \varphi(U(a))\,d\mu(a)\Bigr| \le \Lambda \cdot \|z\|.$$
--
--   Lean: `OAI.Erdos3.jointAffineBoolean_translation_bound` in `lean/OAI/Combinatorics/Progressions/Lattices/JointAffineBooleanSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B033` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/JointAffineBooleanSource.lean#L346

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B033

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}
  (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
  (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
  (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) →L[ℝ]
    (BlockParameter (B d) (Fin (h d)) α → ℝ))
  (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
  (ψ : ℝ → ℝ) (r : ∀ d, B d × Fin (h d) → ℝ) (κ : D → ℝ)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}

theorem jointAffineBoolean_translation_bound
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
    : ImageTranslationBound
      (realDensityMeasure (jointBooleanSource h)
        (jointAffineBooleanCutoff c sets block v sel (fun d => (L d).toContinuousLinearMap) b ψ r κ))
      (jointAffineBooleanSampler c sets L b)
      (jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H) := by
  sorry

end Erdos3
end
end OAI
