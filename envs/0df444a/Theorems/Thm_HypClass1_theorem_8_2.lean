-- Prove2me | Theorems.Thm_HypClass1_theorem_8_2
-- name    : HypClass1.theorem_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:30:45.581209+00:00
-- url     : https://prove2.me/theorems/58bd4f5e-d200-4b61-9974-cf9879ab47d5
-- title:
--   Theorem 8.2 ([25, Cor. 1.6]) — $\chi'(H)\le D_1+D_1(D_1/D_2)^{-1/3-\eta}$ for bounded codegree
-- statement:
--   Let $0 < \gamma, \mu < 1$ and $0 < \eta < 1/96$. There is $N_0 = N_0(\gamma, \eta, \mu)$ such that the following holds for all $N \ge N_0$ and all reals $D_1, D_2 > 0$ with $D_1 \ge \exp(\log^\mu N)$: if $H$ is a 3-graph on $N$ vertices with maximum degree at most $D_1$ and codegree at most $D_2 \le D_1^{1-\gamma}$, then
--   $$
--   \chi'(H) \le D_1 + D_1 \left(\frac{D_1}{D_2}\right)^{-1/3-\eta}.
--   $$
--
--   This is a result of Kang, Kühn, Methuku and Osthus, quoted by the paper; it is used to colour all but a few edges of the sparse remainder (proof of Theorem 1.2) and in Proposition 8.3.
--
--   **Formalization Note** $N_0$ is chosen before $N$, $D_1$, $D_2$ and $H$; "codegree at most $D_2$" is $\Delta_2(H) \le D_2$.
--
--   Differences from the source:
--   - reading: log (base not named) → natural logarithm Real.log; reason: standard convention; paper.md decision 6
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Theorem 8.2 (quoting [25] Kang–Kühn–Methuku–Osthus, Corollary 1.6), p.33

import Mathlib
import Definitions.Def_HypClass1_K3
import Definitions.Def_MatchVec3_maxDegree
import Definitions.Def_HypClass1_maxCodeg
import Definitions.Def_HypClass1_chromaticIndex

namespace HypClass1

/-- **Theorem 8.2 (Kang–Kühn–Methuku–Osthus, [25, Corollary 1.6], as quoted).** Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Theorem 8.2, p.33:
"Let D₁, D₂, N > 0, and let 0 < γ, µ < 1, and let 0 < η < 1/96. Then there exists N₀ = N₀(γ, η, µ)
such that the following holds for all N ≥ N₀ and D₁ ≥ exp(log^µ N). Let H be a 3-graph on N vertices
with maximum degree at most D₁ and codegree at most D₂ ≤ D₁^{1−γ}. Then the chromatic index of H is
at most D₁ + D₁(D₁/D₂)^{−1/3−η}."

**Formalization Note.** `N₀` depends only on `γ, η, µ` (chosen before `N, D₁, D₂, H`). `D₁, D₂` are
positive reals; `H` is a 3-graph on `Fin N`; "codegree at most D₂" is `∆₂(H) ≤ D₂`. Powers are real
powers, `log` natural. -/
theorem theorem_8_2 (γ μ η : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hη0 : 0 < η) (hη1 : η < 1 / 96) :
    ∃ N₀ : ℕ, ∀ N : ℕ, 0 < N → N₀ ≤ N → ∀ D₁ D₂ : ℝ, 0 < D₁ → 0 < D₂ →
      Real.exp (Real.log N ^ μ) ≤ D₁ →
      ∀ H : Finset (Finset (Fin N)), H ⊆ K3 (Fin N) →
        (MatchVec3.maxDegree H : ℝ) ≤ D₁ → (maxCodeg H : ℝ) ≤ D₂ → D₂ ≤ D₁ ^ (1 - γ) →
        (chromaticIndex H : ℝ) ≤ D₁ + D₁ * (D₁ / D₂) ^ (-1 / 3 - η) := by sorry

end HypClass1
