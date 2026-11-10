-- Prove2me | Theorems.Thm_KnownFidelity_Rank_proposition_4_1
-- name    : KnownFidelity.Rank.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:47:52.648462+00:00
-- url     : https://prove2.me/theorems/01817d30-4867-4a15-8f8c-7817fbc2f399
-- title:
--   Proposition 4.1 — hard instances for the maximally mixed reference
-- statement:
--   There are universal constants $\gamma,c>0$ and $j_0\in\mathbb N$ such that, for every $j\ge j_0$, there are priors $\Lambda_0,\Lambda_1$ on states on $\mathbb C^j$ and an integer $m\ge cj^2/\log^4(j+1)$ satisfying
--
--   $$T_j(\tau):=\frac{\mathrm{tr}\sqrt\tau}{\sqrt j}\le\frac\gamma4\quad\Lambda_0\text{-a.s.},\qquad T_j(\tau)\ge\gamma\quad\Lambda_1\text{-a.s.},$$
--
--   and, for every integer $0\le t\le m$,
--
--   $$d_{\mathrm{tr}}\big(\mathbb E_{\Lambda_0}\tau^{\otimes t},\,\mathbb E_{\Lambda_1}\tau^{\otimes t}\big)\le\frac1{100}.$$
--
--   The two priors separate the fidelity with $I_j/j$ by a constant factor, yet their $t$-copy averages are almost indistinguishable for $t$ up to order $j^2$; this is the core of every lower bound in the paper. Logarithms are natural.
--
--   Differences from the source:
--   - encoding: priors on states and the average states E_Λ τ^{⊗t} → IsStatePrior (probability measure, a.s. a density matrix) and avgPower Λ id t (entrywise integrals); reason: the same objects; the a.s. state condition keeps every integral genuine
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, Proposition 4.1, p. 8 (PDF p. 10)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_IsStatePrior
import Definitions.Def_KnownFidelity_Rank_avgPower
import Definitions.Def_KnownFidelity_Rank_Tj
import Definitions.Def_KnownFidelity_Rank_traceDist

open MeasureTheory

namespace KnownFidelity.Rank

/-- **Proposition 4.1 (Hard instances for the maximally mixed reference).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, Proposition 4.1, printed p. 8 (PDF p. 10): "There are universal constants γ, c > 0 and
j₀ ∈ N such that, for every j ≥ j₀, there are priors Λ₀, Λ₁ on states on C^j and an integer
m ≥ cj²/log⁴(j + 1) satisfying T_j(τ) := tr √τ/√j ≤ γ/4 Λ₀-a.s., T_j(τ) ≥ γ Λ₁-a.s., and, for
every integer 0 ≤ t ≤ m, d_tr(E_{Λ₀} τ^{⊗t}, E_{Λ₁} τ^{⊗t}) ≤ 1/100."

**Formalization Note.** `γ, c, j₀` come first. A prior on states is `IsStatePrior` (probability
measure carried by density matrices); `E_Λ τ^{⊗t} = avgPower Λ id t`; `T_j = Tj`; `log` is
natural; `d_tr = traceDist`. -/
theorem proposition_4_1 :
    ∃ γ c : ℝ, 0 < γ ∧ 0 < c ∧ ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
      ∃ (Λ₀ Λ₁ : Measure (Matrix (Fin j) (Fin j) ℂ)) (m : ℕ),
        IsStatePrior Λ₀ ∧ IsStatePrior Λ₁ ∧
        c * (j : ℝ) ^ 2 / Real.log (j + 1) ^ 4 ≤ m ∧
        (∀ᵐ τ ∂Λ₀, Tj τ ≤ γ / 4) ∧ (∀ᵐ τ ∂Λ₁, γ ≤ Tj τ) ∧
        ∀ t : ℕ, t ≤ m → traceDist (avgPower Λ₀ id t) (avgPower Λ₁ id t) ≤ 1 / 100 := by sorry

end KnownFidelity.Rank
