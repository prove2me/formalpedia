-- Prove2me | Theorems.Thm_HiddenHardCoreColoring_Mixing_fact_21
-- name    : HiddenHardCoreColoring.Mixing.fact_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T09:00:34.804594+00:00
-- url     : https://prove2.me/theorems/c5b51373-8cd5-46be-9ea8-ce0604d5a61c
-- title:
--   Fact 21 — resolvent of the hard-core dynamics: minimizer, three estimates, resolvent identity
-- statement:
--   Let $G$ be a finite simple graph on $n\ge1$ vertices, $\nu$ the hard-core model with activities $\lambda_v>0$ and $H=n(\mathrm{Id}-P^\nu)$ its operator, let $a>0$ and $R=(\mathrm{Id}+aH)^{-1}$. Then $\mathrm{Id}+aH$ is invertible, and:
--   1. For every $h$, $Rh$ is the unique minimizer of $\|g-h\|_\nu^2+a\langle g,Hg\rangle_\nu$ over $g\in L^2(\nu)$.
--   2. For every $h$,
--   $$\|Rh\|_\nu\le\|h\|_\nu,\qquad\|(\mathrm{Id}-R)h\|_\nu^2\le a\langle h,Hh\rangle_\nu,\qquad\langle Rh,HRh\rangle_\nu\le\frac{\langle h,Hh\rangle_\nu}{(1+a\operatorname{gap}(H))^2}.$$
--   3. If $H'$ and $R'=(\mathrm{Id}+aH')^{-1}$ correspond to other positive activities $\lambda'$, then $R'-R=aR'(H-H')R$ as linear maps on $\mathbb R^{\mathcal I}$.
--
--   These are the properties of the resolvent smoothing used in Lemmas 19 and 20. The algebraic identity in 3 is an instance of the published `MarkovEntanglement.resolvent_identity` (with $P=-aH$, $P'=-aH'$), referenced in this mission.
--
--   **Formalization Note** $R$ is the matrix inverse; the first conjunct asserts that $\mathrm{Id}+aH$ is invertible, so $R$ is the actual inverse. Uniqueness is stated as: every $g\ne Rh$ has strictly larger objective.
--
--   Differences from the source:
--   - generalization: ν and H as in Section 3.3, i.e. on the graph G of §3.2 (deg ≤ Δ, standing q ≥ Δ + 3) → any finite simple graph on n ≥ 1 vertices; reason: the statement involves neither Δ nor q; the paper's graph is a special case
--   - encoding: let R := (Id + aH)⁻¹ (invertibility presupposed, shown in the proof) → first conjunct IsUnit (1 + a • H); R is the matrix inverse; reason: Lean's matrix inverse is total; the conjunct makes R the actual inverse
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; Fact 21, p.23; ν and H as in §3.3, p.8

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_HardCore

open Finset Matrix

namespace HiddenHardCoreColoring.Mixing

/-- **Fact 21** (Xiongxin Yang, STOC 2027 submission #964 (October 2026), p.23). Let `ν` and `H` be the hard-core model and its operator with positive
activities `λ`, let `a > 0` and `R := (Id + aH)⁻¹`. Then `Id + aH` is invertible; for every `h`, `Rh` is
the unique minimizer of `‖g − h‖²_ν + a⟨g, Hg⟩_ν`; `‖Rh‖_ν ≤ ‖h‖_ν`; `‖(Id − R)h‖²_ν ≤ a⟨h, Hh⟩_ν`;
`⟨Rh, HRh⟩_ν ≤ ⟨h, Hh⟩_ν/(1 + a gap(H))²`; and for other positive activities `λ'`,
`R' − R = aR'(H − H')R` on `ℝ^ℐ`. -/
theorem fact_21 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (lam : V → ℝ) (hlam : ∀ v, 0 < lam v) (a : ℝ) (ha : 0 < a) :
    IsUnit (1 + a • hcH G lam) ∧
    (∀ h g : IndSet G → ℝ, g ≠ resolvent G lam a *ᵥ h →
      ipNu G lam (resolvent G lam a *ᵥ h - h) (resolvent G lam a *ᵥ h - h) +
          a * ipNu G lam (resolvent G lam a *ᵥ h) (hcH G lam *ᵥ (resolvent G lam a *ᵥ h)) <
        ipNu G lam (g - h) (g - h) + a * ipNu G lam g (hcH G lam *ᵥ g)) ∧
    (∀ h : IndSet G → ℝ,
      Real.sqrt (ipNu G lam (resolvent G lam a *ᵥ h) (resolvent G lam a *ᵥ h)) ≤
        Real.sqrt (ipNu G lam h h)) ∧
    (∀ h : IndSet G → ℝ,
      ipNu G lam ((1 - resolvent G lam a) *ᵥ h) ((1 - resolvent G lam a) *ᵥ h) ≤
        a * ipNu G lam h (hcH G lam *ᵥ h)) ∧
    (∀ h : IndSet G → ℝ,
      ipNu G lam (resolvent G lam a *ᵥ h) (hcH G lam *ᵥ (resolvent G lam a *ᵥ h)) ≤
        ipNu G lam h (hcH G lam *ᵥ h) / (1 + a * hcGapH G lam) ^ 2) ∧
    (∀ lam' : V → ℝ, (∀ v, 0 < lam' v) →
      resolvent G lam' a - resolvent G lam a =
        a • (resolvent G lam' a * (hcH G lam - hcH G lam') * resolvent G lam a)) := by sorry

end HiddenHardCoreColoring.Mixing
