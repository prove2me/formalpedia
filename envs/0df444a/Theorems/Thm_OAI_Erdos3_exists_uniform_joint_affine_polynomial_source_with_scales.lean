-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_uniform_joint_affine_polynomial_source_with_scales
-- name    : OAI.Erdos3.exists_uniform_joint_affine_polynomial_source_with_scales
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T23:46:08.32823+00:00
-- url     : https://prove2.me/theorems/95459ce9-350a-4ec3-af07-0f9c25ac5ed6
-- title:
--   A uniform regularized joint affine Boolean source approximates every polynomial perturbation
-- statement:
--   Let $D$, $\alpha$, $Z$ be finite types with decidable equality, and for each $d \in D$ let $B_d$, $O_d$ be finite types with decidable equality and $O_d$ nonempty (these are section variables). Let $h : D \to \mathbb{N}$ with $h_d > 0$ for all $d$; let $\mathrm{sets}_d : O_d \to \mathrm{Finset}\ \alpha$ be injective with $|\mathrm{sets}_d(o)| \le h_d$; let $\mathrm{block}_d : O_d \to B_d$ be injective; let $c_0, C : D \to \mathbb{R}$ with $c_0(d) > 0$ and $C(d) \ge 0$; let $\psi : \mathbb{R} \to \mathbb{R}$ be $C^\infty$ with values in $[0,1]$, $\psi(t) = 0$ for $|t| \le 1$ and $\psi(t) = 1$ for $|t| \ge 2$; let $A, T \in \mathbb{R}_{\ge 0}$ with $\psi$ $A$-Lipschitz and Mathlib's `Real.smoothTransition` $T$-Lipschitz; let $\mathrm{degree} \in \mathbb{N}$, $C_p \ge 0$, $0 < \delta \le 1$ and $E > 0$. Write $P_d = B_d \times \mathrm{Fin}(h_d) \times \mathrm{Option}\ \alpha$ (`BlockParameter`) and $\Pi = \Sigma_d P_d$ (`JointBlockParameter B h α`). Then there exists $\rho \in \mathbb{R}_{\ge 0}$ with $0 < \rho \le 1$ and $\rho = $ `jointAffineSourceRadius h c₀ C A T δ E`, and there exists a real $t$ with $0 < t \le 1$ and $t = $ `jointAffinePolynomialTolerance h c₀ C A T degree Cp δ E` (both explicit real-valued functions of OpenAI), such that the following holds. For every $c : \forall d, B_d \to \mathbb{R}$ with $c_0(d) \le |c_d(\mathrm{block}_d(o))| \le C(d)$ for all $d, o$, and all $\mathrm{center}, \mathrm{width} : \forall d, P_d \to \mathbb{R}$ with $\mathrm{width}$ nowhere zero, $\delta \le |\mathrm{width}_d(z)|$ and $|\mathrm{center}_d(z)| + |\mathrm{width}_d(z)| \le 1$ for all $d, z$: let $L_d$ be the coordinatewise scaling $x \mapsto (\mathrm{width}_d(z)\,x_z)_z$ on $\mathbb{R}^{P_d}$, let $\mathrm{slice}(x) = \mathrm{center} + \bigoplus_d L_d$ applied to $x \in \mathbb{R}^{\Pi}$ (via `sigmaAxisOperator`), and let $f = $ `regularizedImageDensity (jointBooleanSource h) (jointAffineBooleanSampler c sets L center) ρ`, a function $\mathbb{R}^{\Sigma_d O_d} \to \mathbb{R}$ (OpenAI's mixture of product profiles of width $\rho$ around the images of the joint affine Boolean sampler, averaged over the measure `jointBooleanSource h` on $\mathbb{R}^\Pi$). Then: $f(x) \in [0, \rho^{-|\Sigma_d O_d|}]$ for all $x$; $f$ is integrable with $\int f = 1$; $f$ is `affineProductProfileLip (Σ d, O d) ρ`-Lipschitz (that constant is $|\Sigma_d O_d| \cdot$ `probabilityProfileLipschitz` $\cdot \rho^{-(|\Sigma_d O_d|+1)}$); and for every family $p : \Sigma_d O_d \to \mathbb{R}[\mathrm{PolynomialParameter}\ Z\ \Pi]$ of real multivariate polynomials in the variables $\mathrm{Option}(Z \oplus \Pi)$ with every degree in each variable at most $\mathrm{degree}$ and every coefficient of absolute value at most $C_p$, every $z \in \mathbb{R}^Z$ with $|z_i| \le 1$ for all $i$ such that `parameterPolynomialMap p 0 z` $=$ `jointBooleanSampler h c sets`, and every measurable $\varphi : \mathbb{R}^{\Sigma_d O_d} \to \mathbb{R}$ with $|\varphi| \le 1$,
--   $$\Bigl|\int f\,\varphi - \texttt{mappedTest}\ (\texttt{jointBooleanSource}\ h)\ \bigl(\texttt{parameterPolynomialMap}\ p\ t\ z \circ \mathrm{slice}\bigr)\ \varphi\Bigr| \le E,$$
--   where `mappedTest μ U φ` $= \int \varphi(U(a))\,d\mu(a)$ and `parameterPolynomialMap p t z x` evaluates the polynomials $p$ at the parameter point built from $t$, $z$ and $x$.
--
--   Lean: `OAI.Erdos3.exists_uniform_joint_affine_polynomial_source_with_scales` in `lean/OAI/Combinatorics/Progressions/Polynomial/JointAffinePolynomialSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B033` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/JointAffinePolynomialSource.lean#L21

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B033

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α Z : Type*} [Fintype Z] [DecidableEq Z] [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

theorem exists_uniform_joint_affine_polynomial_source_with_scales
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (degree : ℕ) (Cp : ℝ) (hCp : 0 ≤ Cp)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) {E : ℝ} (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧
    (ρ : ℝ) = jointAffineSourceRadius (B := B) (O := O) (α := α) h c₀ C A T δ E ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    t = jointAffinePolynomialTolerance (Z := Z) (B := B) (O := O) (α := α)
      h c₀ C A T degree Cp δ E ∧
    ∀ (c : ∀ d, B d → ℝ), (∀ d o, c₀ d ≤ |c d (block d o)|) →
    (∀ d o, |c d (block d o)| ≤ C d) →
    ∀ (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
      (hw : ∀ d z, width d z ≠ 0),
    (∀ d z, δ ≤ |width d z|) → (∀ d z, |center d z| + |width d z| ≤ 1) →
    let L := fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv
    let slice := fun x : JointBlockParameter B h α → ℝ =>
      (fun s => center s.1 s.2) + sigmaAxisOperator (fun d => (L d).toContinuousLinearMap) x
    let f := regularizedImageDensity (jointBooleanSource h) (jointAffineBooleanSampler c sets L center) ρ
    (∀ x, f x ∈ Set.Icc (0 : ℝ) (ρ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    Integrable f ∧ (∫ x, f x) = 1 ∧ LipschitzWith (affineProductProfileLip (Σ d, O d) ρ) f ∧
    ∀ p : (Σ d, O d) → MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ,
    (∀ o i, (p o).degreeOf i ≤ degree) → (∀ o m, |(p o).coeff m| ≤ Cp) →
    ∀ z : Z → ℝ, (∀ i, |z i| ≤ 1) →
    parameterPolynomialMap p 0 z = jointBooleanSampler h c sets →
    ∀ φ : ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      |(∫ y, f y * φ y) - mappedTest (jointBooleanSource h) ((parameterPolynomialMap p t z) ∘ slice) φ| ≤ E := by
  sorry

end Erdos3
end
end OAI
