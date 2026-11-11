-- Prove2me | Theorems.Thm_HiddenCorr_ERM_eq_38
-- name    : HiddenCorr.ERM.eq_38
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:36:30.212216+00:00
-- url     : https://prove2.me/theorems/46926a9f-9a21-4de1-a31a-80ae6d374777
-- title:
--   §6.4, Eqs. (37)–(38) — the pseudo-label risk equals marginal means plus the graph covariance estimate
-- statement:
--   Let $G$ be a candidate graph with $n$ vertices on each side, $w^\star$ its optimal weights and $\tilde Y=T_GY$ the pseudo-labels of the observed labels $Y$. For every real observable, with values $f(X_1),\dots,f(X_n)$ on the inputs,
--   $$\frac1n\sum_{i=1}^nf(X_i)\tilde Y_i=\hat\mu_f\hat\mu_Y+Z_f(w^\star)\qquad\text{(Eq. (37))},$$
--   and consequently, for the affine loss $\ell(z,y)=f_1(z)+yf_2(z)$ and every hypothesis $h$,
--   $$\hat L_G(h)=\hat\mu_{f_1\circ h}+\hat\mu_{f_2\circ h}\hat\mu_Y+Z_{f_2\circ h}(w^\star)\qquad\text{(Eq. (38))}.$$
--
--   The identity says that pseudo-label ERM minimizes exactly the loss estimate obtained by combining the graph covariance estimator with the marginal sample means; the learning guarantees are derived from it.
--
--   Differences from the source:
--   - generalization: G matching-covered with a hidden matching, n ≥ 1, f₁, f₂ on Z with the boundedness of Eq. (33) → any edge set E ⊆ Fin n × Fin n, any n, any f₁, f₂ : ℝ → ℝ, any h, X, Y (Eq. (37) for every vector a = (f(Xᵢ))ᵢ); reason: the identity is algebraic (T_G = J + nΠA(w⋆)Π) and uses none of these assumptions; it specializes to the paper's setting
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), p. 25, §6.4, Eqs. (37)–(38)

import Mathlib
import Definitions.Def_IncrementalER_energy
import Definitions.Def_HiddenCorr_ERM_CandidateGraph
import Definitions.Def_HiddenCorr_ERM_Complexity
import Definitions.Def_HiddenCorr_ERM_PseudoLabel

universe u

namespace HiddenCorr.ERM

/-- **§6.4, Eqs. (37)–(38)**, p. 25. For every candidate graph with edge set `E`, every
real observable vector `a = (f(X₁), …, f(Xₙ))` and labels `Y`, with the pseudo-labels
`Ỹ = T_G Y`: `(1/n) ∑ᵢ f(Xᵢ) Ỹᵢ = μ̂_f μ̂_Y + Z_f(w⋆)` (Eq. (37)); consequently the pseudo-label
risk of the affine loss `f₁(z) + y f₂(z)` is
`L̂_G(h) = μ̂_{f₁∘h} + μ̂_{f₂∘h} μ̂_Y + Z_{f₂∘h}(w⋆)` (Eq. (38)). -/
theorem eq_38 {𝒳 : Type u} (n : ℕ) (E : Finset (Fin n × Fin n)) :
    (∀ a Y : Fin n → ℝ,
        (1 / (n : ℝ)) * ∑ i, a i * pseudoLabels E Y i =
          sampleMean a * sampleMean Y + covEst E (wStar E) a Y) ∧
      ∀ (f₁ f₂ : ℝ → ℝ) (h : 𝒳 → ℝ) (X : Fin n → 𝒳) (Y : Fin n → ℝ),
        pseudoRisk E f₁ f₂ h X Y =
          sampleMean (fun i => f₁ (h (X i))) + sampleMean (fun i => f₂ (h (X i))) * sampleMean Y +
            covEst E (wStar E) (fun i => f₂ (h (X i))) Y := by sorry

end HiddenCorr.ERM
