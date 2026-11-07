-- Prove2me | Theorems.Thm_OnlineShadow_LogRate_lemma_4_4
-- name    : OnlineShadow.LogRate.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:16:16.784628+00:00
-- url     : https://prove2.me/theorems/735f2e80-1eb2-4d5f-8c12-6c0bc092a234
-- title:
--   Lemma 4.4 — without bad outcomes every answer is $\varepsilon$-accurate
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Run Algorithm 1 (ONLINESHADOWTOMOGRAPHY1) for $m$ rounds with accuracy $\varepsilon>0$, any logistic sharpness $\lambda$, on $n$ copies of a $d\times d$ density matrix $\rho$, against any adaptive adversary, with an integer mistake budget $K\ge1$ satisfying $K\ge C\log d/\varepsilon^2$.
--
--   **Lemma 4.4.** If over the course of the $m$ rounds no bad outcome occurs, then every estimate the protocol outputs satisfies
--   $$\big|\widehat\mu^{(t)}-\mathrm{Tr}(A^{(t)}\rho)\big|<\varepsilon\qquad(t=1,\dots,m).$$
--
--   Together with Lemma 4.7 this proves Theorem 1.2.
--
--   **Formalization Note** A run is fixed by its outcome string; rounds are numbered from $0$ in Lean.
--
--   Differences from the source:
--   - reading: no hypothesis on K printed; the proof: "provided the constant in K = Θ(log(d)/ε²) is large enough" → ∃ C > 0 (before all other data) with K ≥ C log d/ε²; reason: the proof's requirement, with an absolute constant (paper.md R8)
--   - generalization: λ = Θ(εn/√K) (Algorithm 1's parameter) → any real λ and any n; reason: the outputs do not depend on λ or n once the outcomes are fixed; the paper's λ is a special case
--   - encoding: positive mistake budget K → integer K ≥ 1; reason: Algorithm 1's budget; at K = 0 line 18 never fires
--   - encoding: ε > 0 (Definition 1.1, standing) → explicit hypothesis 0 < ε; reason: standing assumption
--   - encoding: runs of the protocol → outcome strings ω : Fin (2(m+K)) → Bool; rounds numbered from 0; reason: each run is determined by its outcomes (paper.md R11)
--   - encoding: Tr(·) of the product → the real part .trace.re; reason: every such trace is of a Hermitian operator or of a product of two Hermitian operators, so it is real and the real part is its value
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Lemma 4.4, p. 11 (proof p. 12)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_OnlineShadow_LogRate_alg1Run
import Definitions.Def_OnlineShadow_LogRate_alg1Bad

open scoped ComplexOrder

namespace OnlineShadow.LogRate

/-- **Lemma 4.4** (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), p.11; proof p.12). There is an absolute constant `C > 0` such that the following
holds. Run Algorithm 1 with `m` rounds, accuracy `ε > 0`, any sharpness `λ`, on `n` copies of a
density matrix `ρ` on `ℂ^d`, against any adaptive adversary, with an integer mistake budget
`K ≥ max(1, C log d/ε²)`. If no bad outcome occurs during the run, then every estimate satisfies
`|μ̂⁽ᵗ⁾ − Tr(A⁽ᵗ⁾ρ)| < ε`, `t < m`.

**Formalization Note** (paper.md R8) The lemma prints no hypothesis on `K`; its proof ends "provided the
constant in `K = Θ(log(d)/ε²)` is large enough", stated here as `∃ C > 0` before all other data. A run
is fixed by its outcome string `ω` (paper.md R11); rounds are numbered from `0`. -/
theorem lemma_4_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d n m K : ℕ) (ε lam : ℝ), 0 < ε → 1 ≤ K → C * Real.log d / ε ^ 2 ≤ (K : ℝ) →
        ∀ (ρ : Matrix (Fin d) (Fin d) ℂ), WildeQIT.IsDensityOperator ρ →
        ∀ (adv : Adversary d) (ω : Fin (2 * (m + K)) → Bool),
          ¬ alg1Bad n m K ε lam adv ρ ω →
          ∀ t < m, |alg1Out n m K ε lam adv ω t - (alg1Obs n m K ε lam adv ω t * ρ).trace.re| < ε := by sorry

end OnlineShadow.LogRate
