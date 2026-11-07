-- Prove2me | Theorems.Thm_FreeSpencer_theorem_D_1
-- name    : FreeSpencer.theorem_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:06:32.408766+00:00
-- url     : https://prove2.me/theorems/2b16ae27-0fe6-432f-ad36-d0e116e4e8d2
-- title:
--   Theorem D.1, pp.82–83 — uniform derivative bounds
-- statement:
--   Let $n,D\ge1$, $s=n+D+2$, let $\hat A_1,\dots,\hat A_\ell$, $\ell\le n$, be real symmetric contractions of order $D$, and let $E$ be the maximum of $\mathrm{Tr}(HS)+2F(S,\eta_C(S))+\frac{\vartheta}{1-q}\mathrm{Tr}\,S^{1-q}+2\chi\mathrm{Tr}\sqrt S$ over densities, where $0<q\le\frac12$, $0\le\vartheta\le20s$, $s^{-1}\le\chi\le1$. Put
--   $$\mu=2^{-10}s^{-6},\quad M_C=2^{300}s^{60},\quad M_4=2^{1040}s^{200},\quad\gamma_0=2^{-15}.$$
--   For $\|H\|_{op}\le n+1$ and $0\preceq C\preceq I$, $S_*(H,C)\succeq\mu I_D$. On a fixed coefficient support $U$ where $\gamma_0P_U\preceq C\preceq P_U$, the value is smooth and $|D_C^2E(H,C)[V,V]|\le M_C$ if $V=P_UVP_U$, $\|V\|_{HS}\le1$. If $0\preceq Q\preceq C$ and $\|A\|_{HS}\le s^2$, along any interval $I\subseteq[-\frac12,\frac12]$ on which $\|H+tA\|_{op}\le n+1$ and $\gamma_0P_U\preceq C-t^2Q\preceq P_U$,
--   $$|e^{(4)}(t)|\le M_4,\qquad e(t)=E(H+tA,C-t^2Q).$$
--   The same holds for $U=\{0\}$.
--
--   Differences from the source:
--   - encoding: the coefficient support U, P_U, U = {0}; smoothness → U the range of an isometry W, P_U = W Wᵀ, r = 0 for U = {0}; ContDiffAt ℝ ∞ in (H, C₀) at C₀ = WᵀCW through symPart; reason: every subspace is such a range; V is taken symmetric, as a covariance direction
--   - generalization: (D.6) after the setting γ₀P_U ⪯ C ⪯ P_U → no floor on C itself at t = 0, only 0 ⪯ Q ⪯ C and the conditions along I; reason: the page's conditions along I are the ones the bound uses; this specializes to the source
--   - generalization: the two parameter cases of p.82, square (q, ϑ, χ) = (1/2, 127, 1) and rectangular (q, θ, 1/D) → every (q, ϑ, χ) with 0 < q ≤ 1/2, 0 ≤ ϑ ≤ 20s, s⁻¹ ≤ χ ≤ 1; reason: the page states the theorem in the setting (D.1)–(D.3) and derives (D.3) in both cases, and its proofs use only (D.3); both cases satisfy (D.3) when the algorithm runs (n ≥ 32)
--   - encoding: a maximum over densities → sSup over densities; reason: attainment is proved in lemma_5_1 (Lemma 4.4); the set is nonempty and bounded
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Theorem D.1, pp.82–83; (D.1)–(D.3), p.82

import Mathlib
import Definitions.Def_FreeSpencer_covForm
import Definitions.Def_FreeSpencer_Params
import Definitions.Def_FreeSpencer_IsDensity
open scoped Matrix Matrix.Norms.L2Operator ContDiff

namespace FreeSpencer

/-- **Theorem D.1** (The quantitative bounds used by the algorithm), in the setting (D.1)–(D.3), with the
constants (D.4). Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Theorem D.1, pp.82–83; setting p.82.

**Formalization Note** `R(S, C)` of (D.1) is `potObj q ϑ χ`: its `2χ Tr √S` is the `κ` slot. The square
case is `(q, ϑ, χ) = (1/2, 127, 1)`, the same objective as `(1/2, 128, 0)`. A coefficient support `U` is
the range of an isometry `W`, `P_U = W Wᵀ`, and `r = 0` is `U = {0}`, where (D.5) reads `0 ≤ M_C`.
Smoothness is `C^∞` in `(H, C₀)` with `C = W C₀ Wᵀ` at `C₀ = Wᵀ C W`, through the symmetric part. The
fourth derivative is `iteratedDeriv 4`, at each point of `I`. -/
theorem theorem_D_1 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {n ℓ : ℕ} (hn : 1 ≤ n) (hℓ : ℓ ≤ n) (Ah : Fin ℓ → Matrix ι ι ℝ)
    (hAh : IsContrFam Ah) (q ϑ χ : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (hϑ0 : 0 ≤ ϑ)
    (hϑ : ϑ ≤ 20 * sDim n (Fintype.card ι)) (hχ0 : (sDim n (Fintype.card ι))⁻¹ ≤ χ) (hχ : χ ≤ 1) :
    (∀ (H : Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ), H.IsSymm → ‖H‖ ≤ (n : ℝ) + 1 → IsCov C →
      IsMaximizer q ϑ χ Ah H C (optDensity q ϑ χ Ah H C) ∧
      (optDensity q ϑ χ Ah H C -
        constMu (sDim n (Fintype.card ι)) • (1 : Matrix ι ι ℝ)).PosSemidef) ∧
    (∀ (r : ℕ) (W : Matrix (Fin ℓ) (Fin r) ℝ), Wᵀ * W = 1 →
      (∀ (H : Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ), H.IsSymm → ‖H‖ ≤ (n : ℝ) + 1 →
        (C - gamma0 • (W * Wᵀ)).PosSemidef → (W * Wᵀ - C).PosSemidef →
        ContDiffAt ℝ ∞ (fun p : Matrix ι ι ℝ × Matrix (Fin r) (Fin r) ℝ =>
          pot q ϑ χ Ah (symPart p.1) (W * symPart p.2 * Wᵀ)) (H, Wᵀ * C * W) ∧
        ∀ V : Matrix (Fin ℓ) (Fin ℓ) ℝ, V.IsSymm → V = W * Wᵀ * V * (W * Wᵀ) →
          Matrix.trace (Vᵀ * V) ≤ 1 →
          |deriv (deriv fun t : ℝ => pot q ϑ χ Ah H (C + t • V)) 0| ≤
            constMC (sDim n (Fintype.card ι))) ∧
      (∀ (H A : Matrix ι ι ℝ) (C Q : Matrix (Fin ℓ) (Fin ℓ) ℝ) (I : Set ℝ), H.IsSymm → A.IsSymm →
        Q.PosSemidef → (C - Q).PosSemidef →
        Matrix.trace (Aᵀ * A) ≤ (sDim n (Fintype.card ι) ^ 2) ^ 2 →
        I.OrdConnected → I ⊆ Set.Icc (-(1 / 2)) (1 / 2) →
        (∀ t ∈ I, ‖H + t • A‖ ≤ (n : ℝ) + 1 ∧ (C - t ^ 2 • Q - gamma0 • (W * Wᵀ)).PosSemidef ∧
          (W * Wᵀ - (C - t ^ 2 • Q)).PosSemidef) →
        ∀ t ∈ I, |iteratedDeriv 4 (fun r : ℝ => pot q ϑ χ Ah (H + r • A) (C - r ^ 2 • Q)) t| ≤
          constM4 (sDim n (Fintype.card ι)))) := by sorry

end FreeSpencer
