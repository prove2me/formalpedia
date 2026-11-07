-- Prove2me | Theorems.Thm_LowTempGlauber_lemma_4
-- name    : LowTempGlauber.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:48.858448+00:00
-- url     : https://prove2.me/theorems/0f184801-7bc7-4be4-9895-e5743b4fed91
-- title:
--   Lemma 4 — warm-start and $\chi^2$ mixing bounds from an $(A,b)$ weak Poincaré inequality
-- statement:
--   Let $A,R\ge1$ and $b>0$. Let $P$ be a reversible Markov chain on a finite state space $\Omega$ with stationary distribution $\pi$ and nonnegative spectrum, which satisfies an $(A,b)$ weak Poincaré inequality.
--
--   1. If $\sigma$ is a distribution on $\Omega$ with $\sigma(x)\le R\,\pi(x)$ for all $x$, then for every integer $t\ge0$
--   $$\|\sigma P^t-\pi\|_{TV}\le R\bigl(e^{-t/(2A)}+\sqrt b\bigr).$$
--   2. For every probability distribution $\nu$ on $\Omega$ and every integer $t\ge0$,
--   $$\|\nu P^t-\pi\|_{TV}\le\sqrt{\chi^2(\nu\|\pi)}\,\sqrt{\tfrac14e^{-t/A}+b}.$$
--
--   The lemma converts a weak Poincaré inequality into convergence from a warm start, with an error floor of order $\sqrt b$; the second form drives each stage of the annealing schedule in Lemma 12.
--
--   **Formalization Note** "Reversible" is: $P$ is stochastic and in detailed balance with the distribution $\pi$. In part 2 the hypothesis $\nu(x)=0$ whenever $\pi(x)=0$ is added; without it the paper's $\chi^2$ is $+\infty$ and the bound is empty.
--
--   Differences from the source:
--   - generalization: P has nonnegative spectrum → Σ_x π(x) f(x) (Pf)(x) ≥ 0 for every f (published SKWeakPoincare.HasNonnegSpectrum); reason: for π > 0 the two are equivalent because a reversible P is self-adjoint in ℓ²(π); if π has zeros, detailed balance makes P block triangular and nonnegative spectrum of P implies the Lean condition, so the Lean hypothesis is implied by the source’s
--   - encoding: χ²(ν‖π), equal to +∞ when ν(x) > 0 = π(x) → hypothesis ν(x) = 0 whenever π(x) = 0 in part 2; reason: the excluded case is exactly where the source’s bound is +∞ and says nothing; real division would give a junk finite value
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), Lemma 4, p.8 (proof in Appendix A, p.60)

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_SKWeakPoincare_fMean
import Definitions.Def_LowTempGlauber_ChainLayer

namespace LowTempGlauber

open MarkovMixing

/-- Galanis–Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission (manuscript sha256 c41a38ff…), Lemma 4, p.8 (proof in Appendix A, p.60).

Let `A, R ≥ 1` and `b > 0`, and let `P` be a reversible chain on a finite `Ω` with stationary
distribution `π`, nonnegative spectrum and an `(A, b)` weak-Poincaré inequality. Then
(i) for every distribution `σ` with `σ ≤ R π` and every `t ≥ 0`,
`‖σP^t − π‖_TV ≤ R (e^{−t/(2A)} + √b)` (2); and (ii) for every distribution `ν`,
`‖νP^t − π‖_TV ≤ √χ²(ν‖π) · √(e^{−t/A}/4 + b)`.

**Formalization Note.** Reversible = stochastic and in detailed balance with `π`; nonnegative spectrum is the
published `SKWeakPoincare.HasNonnegSpectrum` (positive semidefiniteness in `ℓ²(π)`). In (ii), `ν(x) = 0` wherever `π(x) = 0`
is assumed: otherwise the page's `χ²` is `+∞` and (ii) says nothing, while the real-valued `chiSq`
would take a finite junk value. -/
theorem lemma_4 {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (P : Matrix Ω Ω ℝ) (π : Ω → ℝ)
    (A R b : ℝ) (hA : 1 ≤ A) (hR : 1 ≤ R) (hb : 0 < b)
    (hP : IsStochastic P) (hπ : IsDist π) (hrev : DetailedBalance P π)
    (hspec : SKWeakPoincare.HasNonnegSpectrum π P) (hwp : IsWeakPoincare P π A b) :
    (∀ σ : Ω → ℝ, IsDist σ → (∀ x, σ x ≤ R * π x) → ∀ t : ℕ,
      tvDist (Matrix.vecMul σ (P ^ t)) π ≤ R * (Real.exp (-(t : ℝ) / (2 * A)) + Real.sqrt b)) ∧
    (∀ ν : Ω → ℝ, IsDist ν → (∀ x, π x = 0 → ν x = 0) → ∀ t : ℕ,
      tvDist (Matrix.vecMul ν (P ^ t)) π ≤
        Real.sqrt (chiSq ν π) * Real.sqrt (Real.exp (-(t : ℝ) / A) / 4 + b)) := by sorry

end LowTempGlauber
