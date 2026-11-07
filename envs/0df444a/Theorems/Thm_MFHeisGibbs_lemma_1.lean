-- Prove2me | Theorems.Thm_MFHeisGibbs_lemma_1
-- name    : MFHeisGibbs.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:50.873214+00:00
-- url     : https://prove2.me/theorems/fed8df1e-93af-41bd-b82a-65cd6058788f
-- title:
--   Lemma 1, (38), (39) — $\mathcal E_C$ as an integral of squared commutators
-- statement:
--   Let $f$ be continuous with the KMS relation and $n\ge2$. For every $\beta>0$ and observable $X$,
--
--   $$\mathcal E_C(X)=\sum_{i,\alpha}\int_{\mathbb R}\|[B^{(i,\alpha)}(t),X]\|_\rho^2\,d\mu_\beta(t),\qquad d\mu_\beta(t)=\frac{dt}{\beta\cosh(2\pi t/\beta)},$$
--
--   and $\int_{\mathbb R}e^{it\omega}d\mu_\beta(t)=\frac1{2\cosh(\beta\omega/4)}$, $\mu_\beta(\mathbb R)=\frac12$. At $\beta=0$, $\mathcal E_C(X)=\frac{f(0)^2}2\sum_{i,\alpha}\|[\sigma^{(i,\alpha)},X]\|_\rho^2$.
--
--   This representation of the Dirichlet form is the main tool behind every lower bound on the coherent generator.
--
--   Differences from the source:
--   - encoding: f(0)² → ‖f 0‖²; reason: the KMS relation makes f(0) real, so these agree
--   - encoding: the Dirichlet form and the KMS norm, which are real for these generators → the real part of the complex inner product; reason: Lean's kmsInner is complex-valued
--   - encoding: dμ_β as a measure → the density (β cosh(2πt/β))⁻¹ written in the integrand; reason: same integrals against Lebesgue measure
--   - reading: 'With f(ν) KMS (see Equation (4))' (p.12) → f continuous with the KMS relation only (KMSRel), without |f| ≤ 1 or c⋆ > 0; reason: §2.3 asks only for the KMS condition, and Appendix B (pp.50, 52, 55) applies (37) and Lemma 1 to filters h without the normalization; this is the broader of the two readings, and it contains every f with (4)
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), Lemma 1, (38), (39), p.12 (PDF 13)

import Definitions.Def_MFHeisGibbs_Generators
import Definitions.Def_MFHeisGibbs_KMS

namespace MFHeisGibbs

/-- **Lemma 1**, Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), p.12, with (38), (39) and the `β = 0`
clause. For every observable `X`, `E_C(X) = ∑_{i,α} ∫ ∥[B^(i,α)(t), X]∥²_ρ dμ_β(t)`, with
`dμ_β(t) = dt/[β cosh(2πt/β)]`, `β > 0`; `∫ e^{itω} dμ_β(t) = 1/(2 cosh(βω/4))`; `μ_β(ℝ) = 1/2`;
and at `β = 0`, `E_C(X) = (f(0)²/2) ∑_{i,α} ∥[σ^(i,α), X]∥²_ρ`.

**Formalization Note.** Continuity and the KMS relation of `f` suffice (p.50). The density of `μ_β` is
written out in the integrals. -/
theorem lemma_1 (f : ℝ → ℂ) (hf : KMSRel f) (n : ℕ) (hn : 2 ≤ n) :
    (∀ β : ℝ, 0 < β → ∀ X : Op n,
      dirichlet β (LC β f n) X =
        ∑ i : Fin n, ∑ α : Fin 3, ∫ t : ℝ,
          kmsNormSq β (comm (heisEvol t (Bjump β f i α)) X) *
            (β * Real.cosh (2 * Real.pi * t / β))⁻¹) ∧
    (∀ β : ℝ, 0 < β → ∀ ω : ℝ,
      ∫ t : ℝ, Complex.exp (Complex.I * (t : ℂ) * (ω : ℂ)) *
          ((β * Real.cosh (2 * Real.pi * t / β))⁻¹ : ℝ) =
        ((2 * Real.cosh (β * ω / 4))⁻¹ : ℝ)) ∧
    (∀ β : ℝ, 0 < β → ∫ t : ℝ, (β * Real.cosh (2 * Real.pi * t / β))⁻¹ = 1 / 2) ∧
    (∀ X : Op n, dirichlet 0 (LC 0 f n) X =
        (‖f 0‖ ^ 2 / 2) * ∑ i : Fin n, ∑ α : Fin 3, kmsNormSq 0 (comm (pauliAt i α) X)) := by sorry

end MFHeisGibbs
