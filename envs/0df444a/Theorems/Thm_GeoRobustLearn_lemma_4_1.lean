-- Prove2me | Theorems.Thm_GeoRobustLearn_lemma_4_1
-- name    : GeoRobustLearn.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:26.717132+00:00
-- url     : https://prove2.me/theorems/29c53ffa-3a2f-4e8f-94f6-4f05c3dbd3b2
-- title:
--   Lemma 4.1 — $V=T_sB_f$ is $[0,1]$-valued with zero certificate defect and $\mathbb E|V(x,0)-f(x)|\le CK\sqrt s$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $f\in\mathcal C_K$, $s\in(0,1]$, and $V=T_sB_f$, the Ornstein–Uhlenbeck smoothing of the offset lift on $\mathbb R^{d+1}$. Then:
--
--   1. $0\le V\le1$ everywhere;
--   2. $V$ is differentiable;
--   3. $\|\nabla_xV(x,a)\|_2-\partial_aV(x,a)\le0$ for every $(x,a)\in\mathbb R^{d+1}$;
--   4. $$\mathbb E_{x\sim\gamma}|V(x,0)-f(x)|\le CK\sqrt s.$$
--
--   Smoothing the offset lift thus keeps the certificate constraint exactly while losing only $O(K\sqrt s)$ in $L^1$ error.
--
--   Differences from the source:
--   - reading: "V is smooth (see Section 3.3)" in the proof → Differentiable ℝ V as a conclusion; reason: makes the validity inequality a statement about genuine derivatives (Mathlib's fderiv is 0 at non-differentiable points)
--   - encoding: ℝ^{d+1} ∋ (x, a), T_s, F^{≤k} → Space (d+1) with the offset as last coordinate; the published ou s and truncation k; reason: Lean representation; same objects
--   - encoding: E_{x∼γ}|·(x, 0) − f(x)| → lower Lebesgue integral of ofReal |·|, with no measurability assumed of f; reason: for f ∈ C_K, f agrees with a Borel function off a Borel γ-null set, so the lower integral is the integral
--   - encoding: "for an absolute constant C" → ∃ C > 0 chosen before d, K, f, s; reason: the meaning of an absolute constant
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Lemma 4.1, p.17 (PDF p.17)

import Definitions.Def_GeoRobustLearn_BoundaryVolume
import Definitions.Def_GeoRobustLearn_OffsetLift
import Definitions.Def_GeoRobustLearn_CertDefect

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-- **Lemma 4.1** (Smoothing `B_f` preserves error and zero defect), p.17.

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…).

For an absolute constant `C`: for every `f ∈ C_K` and `s ∈ (0, 1]`, `V = T_s B_f` takes values in
`[0, 1]`, is differentiable, satisfies `‖∇_x V(x, a)‖₂ − ∂_a V(x, a) ≤ 0` at every point of
`ℝ^{d+1}`, and `E_{x∼γ}|V(x, 0) − f(x)| ≤ C K √s`.

**Formalization Note.** `V` is the published `ou s` applied to `offsetLift f` on `Space (d+1)`.
Differentiability of `V` is stated as a conclusion ("`V` is smooth", proof of Lemma 4.1, and §3.3
item 3) so that the validity inequality is about genuine derivatives. The expectation is a lower
Lebesgue integral; no measurability is assumed of `f` (for `f ∈ C_K`, `f` agrees with a Borel
function off a Borel `γ`-null set, so the lower integral is the integral). -/
theorem lemma_4_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (K s : ℝ) (f : Space d → ℝ),
        InCK K f → 0 < s → s ≤ 1 →
        let V : Space (d+1) → ℝ := ou s (offsetLift f)
        (∀ z, 0 ≤ V z ∧ V z ≤ 1) ∧
        Differentiable ℝ V ∧
        (∀ z, gradXNorm V z - offsetDeriv V z ≤ 0) ∧
        ∫⁻ x, ENNReal.ofReal |V (lift x 0) - f x| ∂gaussian d ≤
          ENNReal.ofReal (C * K * Real.sqrt s) := by sorry

end GeoRobustLearn
