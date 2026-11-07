-- Prove2me | Theorems.Thm_MatrixSpencer_lemma_2_1
-- name    : MatrixSpencer.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:57.083495+00:00
-- url     : https://prove2.me/theorems/0c67d94f-e337-44be-92bc-4230f2ee9ca1
-- title:
--   Lemma 2.1 = Lemma A.1, pp.7, 13 — matrix-weighted Poincaré inequality
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$ be a nonempty open convex set and $W:\Omega\to\mathrm{Sym}^{++}_r(\mathbb R)$ a $C^\infty$ matrix weight with $\int_\Omega W\,dx$ finite. Let $\Theta_{ij}(W)=(\partial_iW)W^{-1}(\partial_jW)-\partial_{ij}W$. Suppose that there is $\lambda>0$ with, for all $x\in\Omega$ and $z_1,\dots,z_n\in\mathbb R^r$,
--
--   $$\sum_{i,j=1}^nz_i^\top\Theta_{ij}(W)z_j\ge\lambda\sum_{i=1}^nz_i^\top Wz_i .$$
--
--   Then every $F\in C^1(\Omega;\mathbb R^r)$ with $\int_\Omega F^\top WF\,dx<\infty$ satisfies
--
--   $$\int_\Omega F^\top WF\,dx-\Bigl(\int_\Omega WF\,dx\Bigr)^\top\Bigl(\int_\Omega W\,dx\Bigr)^{-1}\Bigl(\int_\Omega WF\,dx\Bigr)\le\lambda^{-1}\int_\Omega\sum_{i=1}^n(\partial_iF)^\top W(\partial_iF)\,dx,$$
--
--   where the right-hand side may be $+\infty$. The left side is $\mathrm{Var}_W(F)$.
--
--   This is the matrix analogue of the Poincaré inequality that follows from a curvature lower bound. It is applied to the weight $W$ of Lemma 2.6.
--
--   **Formalization Note** The right side is a Lebesgue integral in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: the index set {1, …, r} → any finite type ι; reason: the use on p.27 is ℝ^d ⊗ ℝ^d, indexed by pairs; ι is {1, …, r} up to relabelling
--   - encoding: Var_W(F) = ∫(F − F̄_W)^⊤W(F − F̄_W) → (A.2)'s expanded form, in ℝ≥0∞ with the right side a lintegral; reason: the two forms are equal, and (A.2) says the right side may be +∞; a Bochner right side would be a junk 0
--   - encoding: [Θ_ij(W)] ⪰ λI ⊗ W → the quadratic form (A.1), the page's own form of it; reason: (A.1) is Lemma A.1's statement of the hypothesis
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma 2.1, p.7 (PDF p.9); Lemma A.1, (A.1), (A.2), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_MatrixSpencer_pdV
import Definitions.Def_MatrixSpencer_curvature
open RBMSensitivity (E)
open Matrix
open scoped ContDiff

namespace MatrixSpencer

/-- **Lemma 2.1 = Lemma A.1 (Matrix-weighted Poincaré inequality).**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma 2.1, p.7 (PDF p.9): "Let Ω ⊆ ℝⁿ be a nonempty open convex set, and let W : Ω → Sym⁺⁺_r(ℝ) be a C^∞
matrix weight such that ∫_Ω W(x) dx is finite. Let Θ_ij(W) = (∂ᵢW)W⁻¹(∂ⱼW) − ∂ᵢⱼW, for 1 ≤ i, j ≤ n. Suppose
that there is some λ > 0 such that on Ω there holds [Θ_ij(W)]ⁿᵢ,ⱼ₌₁ ⪰ λI ⊗ W. Then, every F ∈ C¹(Ω; ℝʳ) with
∫_Ω F^⊤WF dx < ∞ satisfies Var_W(F) ≤ λ⁻¹ ∫_Ω Σᵢ (∂ᵢF)^⊤W(∂ᵢF) dg." Its detailed form is Lemma A.1, p.13
(PDF p.15), with (A.1) and (A.2).

**Formalization Note.** `C^∞` is `∞` in `WithTop ℕ∞`, not Lean's `⊤`, which means analytic. The index set
is any finite type `ι`, so that it fits `Fin d × Fin d` in the use on p.27; this is `Fin r` up to
relabelling. The hypothesis on `Θ` is (A.1), quantified over `z₁, …, zₙ`. The left side is (A.2)'s form of
`Var_W(F)`. The right side "may be +∞" (A.2), so it lives in `ℝ≥0∞`, a `lintegral`: a Bochner right side
would be a junk `0` on infinite-energy `F` and the statement would be false. Integrals are against
Lebesgue measure (`volume`) on `Ω`. -/
theorem lemma_2_1 {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ω : Set (E n)) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) (hΩn : Ω.Nonempty)
    (W : E n → Matrix ι ι ℝ)
    (hWsmooth : ∀ a b, ContDiffOn ℝ ∞ (fun x => W x a b) Ω)
    (hWpos : ∀ x ∈ Ω, (W x).PosDef)
    (hWint : ∀ a b, MeasureTheory.IntegrableOn (fun x => W x a b) Ω)
    (lam : ℝ) (hlam : 0 < lam)
    (hΘ : ∀ x ∈ Ω, ∀ z : Fin n → ι → ℝ,
      lam * ∑ i, z i ⬝ᵥ W x *ᵥ z i ≤ ∑ i, ∑ j, z i ⬝ᵥ curvature W i j x *ᵥ z j)
    (F : E n → ι → ℝ) (hF : ∀ a, ContDiffOn ℝ 1 (fun x => F x a) Ω)
    (hFint : MeasureTheory.IntegrableOn (fun x => F x ⬝ᵥ W x *ᵥ F x) Ω) :
    ENNReal.ofReal
        ((∫ x in Ω, F x ⬝ᵥ W x *ᵥ F x) -
          (fun a => ∫ x in Ω, (W x *ᵥ F x) a) ⬝ᵥ
            (Matrix.of fun a b => ∫ x in Ω, W x a b)⁻¹ *ᵥ (fun a => ∫ x in Ω, (W x *ᵥ F x) a)) ≤
      ENNReal.ofReal lam⁻¹ *
        ∫⁻ x in Ω, ENNReal.ofReal (∑ i, pdV i F x ⬝ᵥ W x *ᵥ pdV i F x) := by sorry

end MatrixSpencer
