-- Prove2me | Theorems.Thm_OnlineShadow_LogRate_Supplement_theorem_1_3
-- name    : OnlineShadow.LogRate.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:56:04.03564+00:00
-- url     : https://prove2.me/theorems/e24f8f73-169c-422d-9fe6-4a48fb93a49d
-- title:
--   Theorem 1.3 — dimension-free online shadow tomography with $O(\sqrt m/\varepsilon^2)$ copies
-- statement:
--   In **online shadow tomography** a learner holds $n$ copies of an unknown state $\rho$ on $\mathbb C^d$. An adversary chooses observables $0\preceq A^{(1)},\dots,A^{(m)}\preceq1$ one at a time, each as a function of the transcript of earlier observables and answers; after receiving $A^{(t)}$ the learner, which may measure its copies, must answer $\widehat\mu^{(t)}$ with $|\widehat\mu^{(t)}-\mathrm{Tr}(A^{(t)}\rho)|\le\varepsilon$.
--
--   **Theorem 1.3.** There is an absolute constant $C>0$ such that for every dimension $d$, every number of rounds $m$ and every $\varepsilon>0$ there are a number of copies
--   $$n\le\frac{C\sqrt m}{\varepsilon^2}$$
--   and a continuous-outcome online protocol on $n$ copies such that, for every density matrix $\rho$ on $\mathbb C^d$ and every measurable adaptive adversary, all $m$ answers are within $\varepsilon$ of $\mathrm{Tr}(A^{(t)}\rho)$ simultaneously with probability at least $9/10$. In particular the number of copies does not depend on $d$.
--
--   Together with Theorem 1.2 (the goal of this mission), the minimum of the two rates equals the best known classical rate for adaptive data analysis up to constants.
--
--   **Formalization Note** The protocol performs one complete instrument with outcomes in $\mathbb R$ per round (measurable, adaptive, blind to $\rho$), which contains the paper's Algorithm 2, and is chosen before $\rho$ and the adversary. The success probability is the Lebesgue integral of the outcome density over the event that every answer is accurate.
--
--   Differences from the source:
--   - encoding: n = O(√m/ε²) → ∃ absolute C > 0 chosen before d, m, ε; n ≤ C √m/ε²; reason: the reading the base mission used for Theorem 1.2's O(·); the proof (p.19) gives explicit constants, failure ≤ (32/ε²)·8π²m/(n²ε²) once nε² > 32
--   - encoding: there is a protocol → a ContProtocol: per round one complete instrument with outcomes y ∈ ℝ (Lebesgue), Kraus density and answer map jointly measurable, entrywise integrable completeness ∫ KᴴK dy = 1, adaptive in past observables and outcomes, no ancilla; chosen before ρ and the adversary; reason: Algorithm 2 (Kraus density ϕ_ω(y·1 − Ā), answer y) is such a protocol; requiring the protocol to lie in this class only makes the existence claim harder
--   - encoding: the adversary selects A⁽ᵗ⁺¹⁾ based on the transcript → a deterministic Adversary whose round-t observable is a Borel measurable function of the earlier answers (IsMeasurableAdversary), quantified after ρ; reason: the paper integrates over transcripts with Lebesgue measure (p.19), which presupposes this; without it the success probability of a continuous-outcome protocol is undefined; a randomized adversary is a mixture of deterministic ones
--   - reading: correctly answers m adaptively chosen observables to error ε with probability at least 9/10 → all m answers satisfy |μ̂ − Tr(Aρ)| ≤ ε simultaneously, the probability being the integral over ℝ^m of the outcome density Tr(K_y ρ^{⊗n} K_yᴴ) over that event (in ℝ≥0∞), at least 9/10; reason: Definition 1.1's ≤ ε; 'correctly answers m observables' is the joint event, as in the base mission's Theorem 1.2
--   - encoding: Tr(·) of the product → the real part .trace.re; reason: every such trace is of a positive semidefinite operator or of a product of two Hermitian operators, so it is real and the real part is its value
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Theorem 1.3, p. 3 (restated p. 17)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_OnlineShadow_LogRate_Supplement_IsMeasurableAdversary
import Definitions.Def_OnlineShadow_LogRate_Supplement_contSuccessProb

open scoped ComplexOrder

namespace OnlineShadow.LogRate.Supplement

/-- **Theorem 1.3** (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), p.3; restated p.17, proved pp.18–22). There is a protocol for online shadow
tomography of `d`-dimensional states that, using `n = O(√m/ε²)` copies of the unknown state, correctly
answers `m` adaptively chosen observables to error `ε` with probability at least `9/10`; in particular
the sample complexity is independent of `d`: there is an absolute constant `C > 0` such that for every
`d`, every `m` and every `ε > 0`, some `n ≤ C √m/ε²` and some continuous-outcome online protocol on
`n` copies satisfy: for every density matrix `ρ` on `ℂ^d` and every (measurable) adaptive adversary,
all `m` answers are within `ε` of `Tr(A⁽ᵗ⁾ρ)` simultaneously with probability at least `9/10`.

**Formalization Note** `O(·)` is an absolute constant `C` chosen before `d, m, ε` (the base mission's
reading for Theorem 1.2). The protocol class is `ContProtocol` (one complete instrument with outcomes in
`ℝ` per round, measurable, adaptive, blind to `ρ`), which contains Algorithm 2; it is chosen before `ρ`
and the adversary. The adversary is the published deterministic `Adversary`, restricted to measurable
ones (`IsMeasurableAdversary`) so that the success probability is an integral of a measurable function.
At `m = 0` the statement holds with `n = 0`. -/
theorem theorem_1_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d m : ℕ) (ε : ℝ), 0 < ε →
        ∃ n : ℕ, (n : ℝ) ≤ C * Real.sqrt m / ε ^ 2 ∧
          ∃ P : ContProtocol d n,
            ∀ ρ : Matrix (Fin d) (Fin d) ℂ, WildeQIT.IsDensityOperator ρ →
              ∀ adv : OnlineShadow.LogRate.Adversary d, IsMeasurableAdversary adv →
                (9 / 10 : ENNReal) ≤ contSuccessProb m P ρ adv ε := by sorry

end OnlineShadow.LogRate.Supplement
