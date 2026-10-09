-- Prove2me | Theorems.Thm_OAI_Erdos3_jointAffineBooleanGoodWeight_derivative_budget
-- name    : OAI.Erdos3.jointAffineBooleanGoodWeight_derivative_budget
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:09:41.685263+00:00
-- url     : https://prove2.me/theorems/6763c40c-912f-4f12-b02e-907ef2783baa
-- title:
--   The total L¹ norm of the partial derivatives of the joint good weight is budgeted
-- statement:
--   Let $D$ and $\alpha$ be finite types with decidable equality, and $B,O : D\to$ types, each $B_d$ and $O_d$ finite with decidable equality. Let $h : D\to\mathbb{N}$, and write $\Pi_d$ for `BlockParameter (B d) (Fin (h d)) α`, the product type $B_d\times\{0,\dots,h_d-1\}\times\mathrm{Option}\ \alpha$. Let $c_d : B_d\to\mathbb{R}$, $\mathrm{sets}_d : O_d\to\mathrm{Finset}\ \alpha$, $\mathrm{block}_d : O_d\to B_d$, $v_d\in\{0,\dots,h_d-1\}$ and $\mathrm{sel}_d : O_d\to\mathrm{Option}\ \alpha$ for each $d$, with $|\mathrm{sets}_d(o)|\le h_d$ for all $d,o$. Let $L_d$ be a continuous linear map $\mathbb{R}^{\Pi_d}\to\mathbb{R}^{\Pi_d}$ and $b_d\in\mathbb{R}^{\Pi_d}$ for each $d$, with operator norm $\|L_d\|\le 1$ (sup norms), and assume that for every $d$ and every $x$ in `scalarCubeProductDomain (B d × Fin (h d)) α` (the set of $x : B_d\times\{0,\dots,h_d-1\}\to(\mathrm{Option}\ \alpha\to\mathbb{R})$ each of whose components lies in OpenAI's `scalarCubeDomain α`, the set of $a$ with every `scalarCubeValue a t` in $(0,1)$), all coordinates of $b_d+L_d(\mathrm{flat}(x))$ have absolute value at most $1$, where $\mathrm{flat}$ is the coordinate identification `blockCubeFlatten`. Let $C : D\to\mathbb{R}$ with $C_d\ge 0$ and $|c_d(\mathrm{block}_d(o))|\le C_d$ for all $d,o$. Let $\psi:\mathbb{R}\to\mathbb{R}$ be $C^\infty$ with values in $[0,1]$ and $\psi(t)=0$ for $|t|\le 1$. Let $A,T\ge 0$ (in $\mathbb{R}_{\ge0}$) be such that $\psi$ is $A$-Lipschitz and Mathlib's `Real.smoothTransition` is $T$-Lipschitz. Let $r_d : B_d\times\{0,\dots,h_d-1\}\to\mathbb{R}$ with all values positive, and $\kappa : D\to\mathbb{R}$ with $\kappa_d>0$. Let $G$ be `jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ`, a real function on $\mathbb{R}^{\Sigma_d\Pi_d}$ (the product over $d$ of OpenAI's `affineBooleanCubeGoodWeight` for block $d$, evaluated on the $d$-th block of coordinates). Then
--   $$\sum_{s\in\Sigma_d\Pi_d}\int\big|DG(x)(e_s)\big|\,dx\le\texttt{jointBooleanWeightBudget}\ h\ C\ A\ T\ r\ \kappa,$$
--   where $DG(x)$ is the Fréchet derivative (Mathlib's `fderiv`), $e_s$ is the standard basis vector at $s$, the integral is against Lebesgue measure, and the right side (with these $O$ and $\alpha$) is the real number
--   $$\sum_{d\in D}\Big(\sum_{i}\frac{2\cdot 2^{|\alpha|}(|\alpha|+1)^2\,T}{r_d(i)}+|\Pi_d|\cdot\frac{A}{\kappa_d}\cdot M_d\Big),$$
--   with $i$ ranging over $B_d\times\{0,\dots,h_d-1\}$ and $M_d$ OpenAI's `productMinorDeterminantDerivativeBound` $|\Pi_d|\ |O_d|\ |\alpha|\ h_d\ C_d\ 1$.
--
--   Lean: `OAI.Erdos3.jointAffineBooleanGoodWeight_derivative_budget` in `lean/OAI/Combinatorics/Progressions/Lattices/JointAffineBooleanSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B011` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/JointAffineBooleanSource.lean#L200

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

theorem jointAffineBooleanGoodWeight_derivative_budget {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) →L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ))
    (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (hL : ∀ d, ‖L d‖ ≤ 1)
    (hbox : ∀ d x, x ∈ scalarCubeProductDomain (B d × Fin (h d)) α →
      ∀ z, |(b d + L d (blockCubeFlatten (B d) (Fin (h d)) α x)) z| ≤ 1)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) :
    (∑ s : JointBlockParameter B h α, ∫ x,
      |fderiv ℝ (jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ) x (Pi.single s 1)|) ≤
      jointBooleanWeightBudget (O := O) (α := α) h C A T r κ := by
  sorry

end Erdos3
end
end OAI
