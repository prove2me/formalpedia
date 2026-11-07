-- Prove2me | Theorems.Thm_OnlineShadow_LogRate_lemma_4_9
-- name    : OnlineShadow.LogRate.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:08:45.235205+00:00
-- url     : https://prove2.me/theorems/738c4c5c-3914-41a8-a8f8-27816f06783f
-- title:
--   Lemma 4.9 — a soft measurement raises $\mathsf N$ by $O(L_f^2/n)\,F$
-- statement:
--   Let $\mathcal H=\mathbb C^d$, let $\psi$ be a unit vector on $\mathcal H\otimes\mathcal R$ ($\mathcal R=\mathbb C^r$) purifying the state $\rho=\mathrm{Tr}_{\mathcal R}|\psi\rangle\langle\psi|$, and let $A$ be a single-copy observable with $0\preceq A\preceq1$. On $(\mathcal H\otimes\mathcal R)^{\otimes n}$ let $\overline A$ denote the lift of $A\otimes1_{\mathcal R}$, $\overline X=\overline A-\mathrm{Tr}(A\rho)1$, $\mathsf N$ the number operator and $\mathcal E[\tau]=\frac1n\mathrm{Tr}(\mathsf N\tau)$ the energy relative to $\psi$.
--
--   Let $n\ge1$ and let $f:[0,1]\to(0,1]$ be non-decreasing with $\alpha=\arcsin\sqrt f$ differentiable on $[0,1]$. Let $L,R$ be real numbers with
--   $$\alpha'(x)\le L\sqrt{f(x)}\quad(x\in[0,1]),\qquad f(y)\le R\,f(x)\quad(x,y\in[0,1],\ 0\le y-x\le1/n),$$
--   for instance $L=L_f=\sup_x\alpha'(x)/\sqrt{f(x)}$ and $R=R_f=\sup f(y)/f(x)$.
--
--   **Lemma 4.9.** For $F=f(\overline A)$,
--   $$\Phi_F^\dagger(\mathsf N)-\mathsf N\preceq\frac{R(1+\sqrt R)L^2}{n}\,F .$$
--
--   A measurement of a smooth function of the lifted observable excites few copies, and only in proportion to the probability of its flag outcome.
--
--   Differences from the source:
--   - generalization: L_f = sup α′/√f and R_f = sup f(y)/f(x) → any reals L, R bounding these ratios; reason: with L = L_f, R = R_f it is the paper's statement; the bound increases in L ≥ 0 and R (paper.md R9)
--   - reading: f differentiable → α = arcsin √f differentiable on [0,1] (one-sided at the endpoints, derivWithin); reason: L_f presupposes α′; it implies f = sin²α differentiable (paper.md R9)
--   - encoding: f : [0,1] → (0,1] non-decreasing → f : ℝ → ℝ with 0 < f ≤ 1 and monotone on [0,1]; reason: the spectrum of A̅ lies in [0,1], so values off [0,1] are never used
--   - encoding: any number of copies n → n ≥ 1; reason: 1/n appears in R_f and in the bound
--   - encoding: $|\psi\rangle$ any purification of $\rho$ on $\mathcal H\otimes\mathcal R$ → ψ : Fin d × Fin r → ℂ with ∑ₓ ‖ψ x‖² = 1 for any r, and ρ := Tr_R |ψ⟩⟨ψ| (marginal ψ); reason: the same objects: every purification is a unit vector on ℂ^d ⊗ ℂ^r and every ρ has one with r = d (paper.md R12)
--   - encoding: Φ_F† the adjoint of the channel Φ_F → measChannel F, the formula √F X √F + √(1 − F) X √(1 − F); reason: p. 14, last line of the derivation of Eq. (8), gives this formula for Φ_F†; √F and √(1 − F) are Hermitian, so it is the adjoint
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Lemma 4.9, p. 15

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_OnlineShadow_LogRate_liftObs
import Definitions.Def_OnlineShadow_LogRate_numberOp
import Definitions.Def_OnlineShadow_LogRate_measChannel

open scoped Kronecker ComplexOrder

namespace OnlineShadow.LogRate

/-- **Lemma 4.9** (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), p.15). Let `ψ` be a unit vector on `H ⊗ R`, `A` an effect on `H`, `n ≥ 1`, and
`f : [0,1] → (0,1]` non-decreasing with `α = arcsin(√f)` differentiable on `[0,1]`. Let `L`, `R` be
reals with `α′(x) ≤ L √f(x)` for `x ∈ [0,1]` and `f(y) ≤ R f(x)` for `x, y ∈ [0,1]`, `0 ≤ y − x ≤ 1/n`.
Then for `F = f(Ā ⊗ 1_R)`, `Φ_F†(N) − N ⪯ (R(1 + √R) L²/n) · F`.

**Formalization Note** (paper.md R9) The paper's `L_f = sup α′/√f` and `R_f = sup f(y)/f(x)` are
replaced by any upper bounds `L`, `R`; with `L = L_f`, `R = R_f` this is the paper's statement, and the
right side increases in `L ≥ 0` and `R`. "`f` differentiable" is read as `α` differentiable on
`[0,1]` (one-sided at the endpoints), which the definition of `L_f` presupposes and which implies `f`
differentiable. `f` is a real function whose values off `[0,1]` are irrelevant (the spectrum of `Ā` lies
in `[0,1]`). `n ≥ 1` since `1/n` appears. `Φ_F†` is `measChannel F`. -/
theorem lemma_4_9 {d r : ℕ} (ψ : Fin d × Fin r → ℂ) (hψ : ∑ x, ‖ψ x‖ ^ 2 = 1) (n : ℕ) (hn : 1 ≤ n)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : ShadowTomography.UpperBound.IsEffect A)
    (f : ℝ → ℝ) (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < f x ∧ f x ≤ 1)
    (hmono : MonotoneOn f (Set.Icc (0 : ℝ) 1))
    (hα : DifferentiableOn ℝ (fun x => Real.arcsin (Real.sqrt (f x))) (Set.Icc (0 : ℝ) 1))
    (L R : ℝ)
    (hL : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      derivWithin (fun x => Real.arcsin (Real.sqrt (f x))) (Set.Icc (0 : ℝ) 1) x ≤
        L * Real.sqrt (f x))
    (hR : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ y - x → y - x ≤ 1 / (n : ℝ) →
      f y ≤ R * f x) :
    let F := cfc f (liftObs n (A ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ)))
    ((((R * (1 + Real.sqrt R) * L ^ 2 / n : ℝ)) : ℂ) • F -
      (measChannel F (numberOp ψ n) - numberOp ψ n)).PosSemidef := by sorry

end OnlineShadow.LogRate
