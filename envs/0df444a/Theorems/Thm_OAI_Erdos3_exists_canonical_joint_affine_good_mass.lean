-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_canonical_joint_affine_good_mass
-- name    : OAI.Erdos3.exists_canonical_joint_affine_good_mass
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T11:09:56.414148+00:00
-- url     : https://prove2.me/theorems/6d6820cf-31c2-4fb9-930c-c86655398402
-- title:
--   A canonical selection gives the joint affine Boolean good weight mass at least 1 − Σ η_d
-- statement:
--   Let $D$ and $\alpha$ be finite types ($\alpha$ with decidable equality), and $B,O : D\to$ types, each $B_d$ and $O_d$ finite with decidable equality and each $O_d$ nonempty. Let $h : D\to\mathbb{N}$ with $h_d>0$ for every $d$. Let $c_d : B_d\to\mathbb{R}$ for each $d$; let $\mathrm{sets}_d : O_d\to\mathrm{Finset}\ \alpha$ be injective with $|\mathrm{sets}_d(o)|\le h_d$ for all $d,o$; let $\mathrm{block}_d : O_d\to B_d$ be injective for each $d$; let $c_0 : D\to\mathbb{R}$ with $c_0(d)>0$ and $c_0(d)\le|c_d(\mathrm{block}_d(o))|$ for all $d,o$. Let $\psi:\mathbb{R}\to\mathbb{R}$ be $C^\infty$ with values in $[0,1]$, $\psi(t)=0$ for $|t|\le 1$ and $\psi(t)=1$ for $|t|\ge 2$. Write $\Pi_d$ for `BlockParameter (B d) (Fin (h d)) α`, the product type $B_d\times\{0,\dots,h_d-1\}\times\mathrm{Option}\ \alpha$. Then there exists $\mathrm{sel}$, assigning to each $d$ a map $O_d\to\mathrm{Option}\ \alpha$, such that for every real $\delta>0$, every $\eta : D\to\mathbb{R}$ with $\eta_d>0$ for all $d$, and all $\mathrm{center},\mathrm{width}$ assigning to each $d$ a function $\Pi_d\to\mathbb{R}$, with $\mathrm{width}_d(z)\ne 0$, $\delta\le|\mathrm{width}_d(z)|$ and $|\mathrm{center}_d(z)|+|\mathrm{width}_d(z)|\le 1$ for all $d$ and $z\in\Pi_d$, we have
--   $$1-\sum_{d\in D}\eta_d\le\int G(x)\,dx,$$
--   the integral being against Lebesgue measure on $\mathbb{R}^{\Sigma_d\Pi_d}$, where $G$ is `jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ` (the product over $d$ of OpenAI's `affineBooleanCubeGoodWeight` for block $d$, evaluated on the $d$-th block of coordinates) with: $v_d=0\in\{0,\dots,h_d-1\}$; $L_d$ the diagonal linear map multiplying the coordinate $z$ by $\mathrm{width}_d(z)$ (`coordinateScaleEquiv`); $b_d=\mathrm{center}_d$; the radius $r_d$ constant equal to `scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)` (the real number $(\eta_d/2)/\big(K_\alpha(|B_d|h_d+1)\big)$ with OpenAI's constant `scalarCubeBoundaryConstant α` as $K_\alpha$); and $\kappa_d$ equal to `canonicalAffineCubeMinorThreshold (O d) α (h d) (c₀ d) δ (η d)`, a real number defined by OpenAI from these parameters.
--
--   Lean: `OAI.Erdos3.exists_canonical_joint_affine_good_mass` in `lean/OAI/Combinatorics/Progressions/Lattices/JointAffineBooleanSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B011` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/JointAffineBooleanSource.lean#L450

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B011

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

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α : Type*} [Fintype D] [Fintype α] [decidableEqAlpha : DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

theorem exists_canonical_joint_affine_good_mass
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hc : ∀ d o, c₀ d ≤ |c d (block d o)|)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1) :
    ∃ sel : ∀ d, O d → Option α, ∀ (δ : ℝ) (η : D → ℝ), 0 < δ → (∀ d, 0 < η d) →
      ∀ (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
        (hw : ∀ d z, width d z ≠ 0),
      (∀ d z, δ ≤ |width d z|) → (∀ d z, |center d z| + |width d z| ≤ 1) →
      1 - ∑ d, η d ≤ ∫ x, jointAffineBooleanGoodWeight c sets block
        (fun d => (⟨0, hh d⟩ : Fin (h d))) sel
        (fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv.toContinuousLinearMap)
        center ψ (fun d _ => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2))
        (fun d => canonicalAffineCubeMinorThreshold (O d) α (h d) (c₀ d) δ (η d)) x := by
  sorry

end Erdos3
end
end OAI
