-- Prove2me | Theorems.Thm_FreeSpencer_lemma_5_5
-- name    : FreeSpencer.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:07:58.711211+00:00
-- url     : https://prove2.me/theorems/a13d3932-854b-42d7-8daa-4579b1df8df3
-- title:
--   Lemma 5.5, pp.36–37 — the normalized Kraus matrices
-- statement:
--   Let $0\preceq C\preceq I_\ell$, $t\ge0$. Let $S\succ0$ have $\mathrm{Tr}\,S\le1$ and $\eta_C(S)\succ0$, with transport $Z$, and put $\Gamma(S)(u,w)=\mathrm{Tr}(S\hat A(u)Z\hat A(w))$. If $\Gamma(S)|_{\mathrm{ran}\,C}\preceq tI$, then with $F_a=2^{-1/2}J_P^{1/2}(D_a)$, $\Sigma=\sum_a|F_a\rangle\langle F_a|$:
--   $$\langle F_a,F_b\rangle=\mathrm{Tr}(PD_aD_b)=\Gamma'_{ab},\quad0\preceq\Sigma\preceq t\,\mathrm{Id},$$
--   $$\mathrm{Tr}_{HS}\Sigma=\mathrm{Tr}\,P=F(S,\eta_C(S))=\mathrm{Tr}(C\Gamma)\le\sqrt\ell,\quad\mathrm{Tr}\,R^2\le\mathrm{Tr}\,\eta_C(S)\le\ell,$$
--   where $\Gamma'=C^{1/2}\Gamma C^{1/2}$, together with $\Phi(P)=P$, and the local unconstrained response $\sum_a\frac12\langle B'_a,(H^{\mathrm{original}})^{-1}B'_a\rangle$ equals $\mathrm{Tr}_{HS}(\Sigma\tilde H^{-1})$. At the maximizing density of the square potential the same holds with $\Gamma$ the derivative in the covariance, and
--   $$\mathrm{Tr}(CJ)\le\mathrm{Tr}_{HS}(\Sigma\tilde H^{-1}).$$
--   This identifies the no-spike condition with the frame bound used in the curvature estimate.
--
--   Differences from the source:
--   - generalization: the block matrices Âᵢ = diag(Aᵢ, −Aᵢ) → any real symmetric contractions on a finite index type ι; reason: the analysis uses nothing about the blocks (p.30); ι = Fin m ⊕ Fin m with liftFam is the source
--   - encoding: Γ′ = C^{1/2} Γ C^{1/2}, Tr(CΓ), and (H^original)⁻¹ → the form at the columns C^{1/2}eₐ, the sum of its diagonal, and symmetric solutions Y a; reason: the page defines them so (p.37)
--   - encoding: J, Γ as derivatives (5.3); Tr(CJ) = Σₐ J(C^{1/2}eₐ, C^{1/2}eₐ) (p.31) → iterated deriv along lines of the potential, and the sum over the columns of MatrixLewis.mpow (1/2) C; reason: the same quantities; smoothness is in lemma_5_1 and theorem_D_1
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 5.5, pp.36–37; Lemma 5.4, pp.34–35

import Mathlib
import Definitions.Def_FreeSpencer_KrausFacts
import Definitions.Def_FreeSpencer_IsDensity
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- **Lemma 5.5** (The normalized Kraus matrices), all clauses (5.12)–(5.15) and the closing version
for subnormalized `S`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 5.5, pp.36–37; notation of Lemma 5.4, pp.34–35.

**Formalization Note** The first group is the closing paragraph: arbitrary `S ≻ 0`, `Tr S ≤ 1`,
`η_C(S) ≻ 0`, with `Γ(S)` the right side of (5.8); the local unconstrained response is
`∑ₐ ½⟨B'ₐ, (H^original)⁻¹ B'ₐ⟩`, the inverse written through symmetric solutions `Y a`. The second group
is at the maximizer, with `Γ` the derivative in the covariance. `H̃⁻¹` is the inverse on the full real
matrix space (p.30). -/
theorem lemma_5_5 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {ℓ : ℕ} (Ah : Fin ℓ → Matrix ι ι ℝ) (hAh : IsContrFam Ah) (θ : ℝ)
    (hθ : 0 < θ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) (hC : IsCov C) (t : ℝ) (ht : 0 ≤ t) :
    (∀ S Z : Matrix ι ι ℝ, S.PosDef → Matrix.trace S ≤ 1 → (covMap Ah C S).PosDef → Z.PosDef →
      Z * covMap Ah C S * Z = S →
      (∀ u, InRan C u → gammaAt Ah S Z u u ≤ t * (u ⬝ᵥ u)) →
      KrausFacts Ah C S Z t (gammaAt Ah S Z) ∧
      ∃ Y : Fin ℓ → Matrix ι ι ℝ,
        (∀ a, (Y a).IsSymm ∧ opH θ Ah C S Z (covMap Ah C S) (Y a) = krausB Ah C a) ∧
        ∑ a, (1 / 2) * Matrix.trace (krausB Ah C a * Y a) =
          trHS (opSigma (balP Z S) (balD Ah C Z) *
            Ring.inverse (opHtilde θ (balP Z S) (balR Z S) (balD Ah C Z)))) ∧
    (∀ H S Z : Matrix ι ι ℝ, H.IsSymm → IsMaximizer (1 / 2) θ 0 Ah H C S → S.PosDef →
      (covMap Ah C S).PosDef → Z.PosDef → Z * covMap Ah C S * Z = S →
      NoSpike (1 / 2) θ 0 Ah H C t →
      KrausFacts Ah C S Z t (covForm (1 / 2) θ 0 Ah H C) ∧
      TrCJ (1 / 2) θ 0 Ah H C ≤
        trHS (opSigma (balP Z S) (balD Ah C Z) *
          Ring.inverse (opHtilde θ (balP Z S) (balR Z S) (balD Ah C Z)))) := by sorry

end FreeSpencer
