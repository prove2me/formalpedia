-- Prove2me | Theorems.Thm_OAI_Erdos3_slicedPrincipalC2Tolerance_spec_s2
-- name    : OAI.Erdos3.slicedPrincipalC2Tolerance_spec_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:29:34.089418+00:00
-- url     : https://prove2.me/theorems/9a5d8e16-614a-4d1d-8bd4-354fc5210484
-- title:
--   A C2-close perturbation of the joint sliced principal map changes image test means by at most η
-- statement:
--   Let $D$ be a finite type and $B_d, F_d$ ($d \in D$) finite types with decidable equality, and let $m$ be a natural number with $|F_d| \le m$ for every $d$. Let $C, a, \delta, \eta$ be real numbers with $C \ge 0$, $a > 0$, $0 < \delta \le 1$, $\eta > 0$, and let $A \in \mathbb{R}_{\ge 0}$ be such that `Real.smoothTransition` is $A$-Lipschitz. Write $\Sigma = \Sigma_d\, (B_d \times F_d)$ and let
--   $$t = \texttt{slicedPrincipalC2Tolerance}\ |\Sigma|\ |D|\ m\ C\ a\ \delta\ A\ \eta,$$
--   an explicit real number defined by OpenAI. Then $0 < t \le 1$, and the following holds.
--
--   Let $c_d : B_d \to \mathbb{R}$, $\mathrm{lower}_d, \mathrm{width}_d : B_d \times F_d \to \mathbb{R}$ ($d \in D$), and choose $b_d \in B_d$, $i_d \in F_d$ for every $d$. Suppose:
--   - $|\mathrm{lower}_d(p)| + |\mathrm{width}_d(p)| \le 1$ for all $d, p$;
--   - $\sum_{b} |c_d(b)| \le C$ and $a \le |c_d(b_d)|$ for every $d$;
--   - $\delta \le \mathrm{width}_d(b_d, j)$ for all $d, j$;
--   - $0 \le \mathrm{lower}_d(b_d, j)$ for all $d$ and all $j \ne i_d$.
--
--   Let $\Phi$ = `jointSlicedPrincipal c lower width` $: \mathbb{R}^{\Sigma} \to \mathbb{R}^{\Sigma_{d \in D} \mathrm{Unit}}$ (a smooth map defined by OpenAI, combining one principal slice map per $d$). Let $V : \mathbb{R}^{\Sigma} \to \mathbb{R}^{\Sigma_{d} \mathrm{Unit}}$ be $C^2$ such that for every $x$ with $|x_p| \le 1$ for all $p$:
--   $$\lVert V(x) - \Phi(x) \rVert \le t,\qquad \lVert DV(x) - D\Phi(x) \rVert \le t,\qquad \lVert D^2V(x) - D^2\Phi(x) \rVert \le t$$
--   (with $D$ the Fréchet derivative, $D^2$ the derivative of the derivative, and operator norms). Then for every measurable $\varphi : \mathbb{R}^{\Sigma_d \mathrm{Unit}} \to \mathbb{R}$ with $|\varphi| \le 1$ everywhere,
--   $$\Bigl| \int \varphi(\Phi(x))\, d\lambda(x) - \int \varphi(V(x))\, d\lambda(x) \Bigr| \le \eta,$$
--   where $\lambda$ = `unitBoxMeasure Σ` is Lebesgue measure restricted to the box $(0, 1]^{\Sigma}$ (and $\int \varphi(U(x))\,d\lambda(x)$ is OpenAI's `mappedTest λ U φ`).
--
--   Lean: `OAI.Erdos3.slicedPrincipalC2Tolerance_spec_s2`, which states OpenAI's `OAI.Erdos3.slicedPrincipalC2Tolerance_spec` (in `lean/OAI/Combinatorics/Progressions/Estimates/JointBooleanStability.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B066`, `OAIE3v2B067` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/JointBooleanStability.lean (declaration OAI.Erdos3.slicedPrincipalC2Tolerance_spec)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B066
import Definitions.Def_OAIE3v2B067

section

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

theorem slicedPrincipalC2Tolerance_spec_s2
    {D : Type*} [Fintype D] {B F : D → Type*}
    [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]
    {m : ℕ} (hdegree : ∀ d, Fintype.card (F d) ≤ m)
    {C a δ η : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) :
    let t := slicedPrincipalC2Tolerance (Fintype.card (Σ d, B d × F d)) (Fintype.card D) m C a δ A η
    0 < t ∧ t ≤ 1 ∧
    ∀ (c : ∀ d, B d → ℝ) (lower width : ∀ d, B d × F d → ℝ)
      (b : ∀ d, B d) (i : ∀ d, F d),
      (∀ d p, |lower d p| + |width d p| ≤ 1) →
      (∀ d, (∑ b, |c d b|) ≤ C) → (∀ d, a ≤ |c d (b d)|) →
      (∀ d j, δ ≤ width d (b d, j)) →
      (∀ d j, j ≠ i d → 0 ≤ lower d (b d, j)) →
      ∀ V : ((Σ d, B d × F d) → ℝ) → ((Σ _d : D, Unit) → ℝ),
      ContDiff ℝ 2 V →
      (∀ x, (∀ p, |x p| ≤ 1) →
        ‖V x - jointSlicedPrincipal c lower width x‖ ≤ t ∧
        ‖fderiv ℝ V x - fderiv ℝ (jointSlicedPrincipal c lower width) x‖ ≤ t ∧
        ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ (jointSlicedPrincipal c lower width)) x‖ ≤ t) →
      ∀ φ : ((Σ _d : D, Unit) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        |mappedTest (unitBoxMeasure (Σ d, B d × F d)) (jointSlicedPrincipal c lower width) φ -
          mappedTest (unitBoxMeasure (Σ d, B d × F d)) V φ| ≤ η := by
  sorry

end Erdos3

end

end OAI
end
