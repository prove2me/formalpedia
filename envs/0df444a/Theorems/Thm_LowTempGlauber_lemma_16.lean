-- Prove2me | Theorems.Thm_LowTempGlauber_lemma_16
-- name    : LowTempGlauber.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:57.784972+00:00
-- url     : https://prove2.me/theorems/5ccb2e4d-db2e-47a0-85de-88f26f6eb997
-- title:
--   Lemma 16 — coupling the warm-start annealing statistics to independent samples, failure $\le m^2|R_H|(e^{-T/(2A)}+\sqrt b)$
-- statement:
--   In the setting of §3.3 ($\Omega$ finite and nonempty, $w>0$, $H:\Omega\to[-H_{\max},H_{\max}]$ with range $R_H$), let $\delta\in(0,1/4)$ and $1/h\ge10H_{\max}\log(4/\delta)$; for $t_0\in\mathbb R$ and an integer $m\ge1$ let $t_i=t_0+ih$. For $i=1,\dots,m$ let $P_i$ be a reversible Markov chain with stationary distribution $\mu_{t_i}$ and nonnegative spectrum satisfying an $(A,b)$ weak Poincaré inequality, with $A,b>0$ independent of $i$. Let $X_0\sim\mu_{t_0}$ and, for $i=1,\dots,m$, let $X_i$ be obtained by running $P_i$ for $T$ steps from $X_{i-1}$. Then there is a coupling of $(X_0,\dots,X_m)$ with independent $Y_0,\dots,Y_m$, $Y_i\sim\mu_{t_i}$, such that
--   $$\Pr\bigl[H(X_i)\ne H(Y_i)\text{ for some }i=0,1,\dots,m\bigr]\le m^2|R_H|\bigl(e^{-T/(2A)}+\sqrt b\bigr).$$
--
--   Since the estimator of Lemma 15 depends on the samples only through $H$, this lets a single warm-start annealing run replace independent exact samples.
--
--   **Formalization Note** The coupling is a joint distribution of the two sequences whose marginals are the path law of $(X_i)$ and the product law of $(Y_i)$. "Reversible" is: stochastic and in detailed balance with $\mu_{t_i}$.
--
--   Differences from the source:
--   - encoding: a coupling of the statistics H(X₀), …, H(X_m) with H(Y₀), …, H(Y_m) → a coupling of the sequences (X_i) and (Y_i); reason: equivalent: a coupling of sequences induces one of the statistics, and a coupling of the statistics lifts to one of the sequences by sampling each sequence conditionally on its statistics
--   - encoding: a finite space Ω → a finite nonempty type Ω; reason: μ_t is a probability distribution only on a nonempty space
--   - encoding: P_i has nonnegative spectrum → Σ_x μ_{t_i}(x) f(x) (P_i f)(x) ≥ 0 for every f (published SKWeakPoincare.HasNonnegSpectrum); reason: μ_{t_i} > 0 and P_i is reversible, hence self-adjoint in ℓ²(μ_{t_i}); the two conditions are equivalent
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), Lemma 16, p.17; setup §3.3, p.15

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_SKWeakPoincare_fMean
import Definitions.Def_LowTempGlauber_ChainLayer
import Definitions.Def_LowTempGlauber_Gibbs

namespace LowTempGlauber

open MarkovMixing

/-- Galanis–Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission (manuscript sha256 c41a38ff…), Lemma 16, p.17, in the setting of §3.3, p.15.

Let `Ω` be finite with weights `w > 0` and Hamiltonian `H : Ω → [−H_max, H_max]` with range `R_H`. Let
`δ ∈ (0, 1/4)` and `1/h ≥ 10 H_max log(4/δ)`; for `t₀ ∈ ℝ` and an integer `m ≥ 1` let `t_i = t₀ + ih`.
Let `P_i` be a reversible chain with stationary distribution `μ_{t_i}` and nonnegative spectrum,
satisfying an `(A, b)` weak-Poincaré inequality for fixed `A, b > 0`. Let `X₀ ∼ μ_{t₀}` and, for
`i = 1, …, m`, obtain `X_i` by running `P_i` for `T` steps from `X_{i−1}`. Then `H(X₀), …, H(X_m)` can
be coupled with `H(Y₀), …, H(Y_m)`, where `Y₀, …, Y_m` are independent with `Y_i ∼ μ_{t_i}`, so that
`Pr[H(X_i) ≠ H(Y_i) for some i] ≤ m² |R_H| (e^{−T/(2A)} + √b)`.

**Formalization Note.** The coupling is a joint law `q` of the two sequences `(X_i)` and `(Y_i)`
(`IsCoupling` of the path law and the product law); it induces the coupling of the statistics, and
conversely a coupling of the statistics lifts to one of the sequences. Reversible = stochastic and in
detailed balance. `Ω` is nonempty so that `μ_t` is a distribution. -/
theorem lemma_16 {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] (w H : Ω → ℝ)
    (hw : ∀ x, 0 < w x) (Hmax : ℝ) (hH : ∀ x, |H x| ≤ Hmax) (δ h : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 4) (hh : 10 * Hmax * Real.log (4 / δ) ≤ 1 / h) (t₀ : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (P : ℕ → Matrix Ω Ω ℝ) (A b : ℝ) (hA : 0 < A) (hb : 0 < b)
    (hP : ∀ i : ℕ, 1 ≤ i → i ≤ m →
      IsStochastic (P i) ∧ DetailedBalance (P i) (muT w H (t₀ + i * h)) ∧
        SKWeakPoincare.HasNonnegSpectrum (muT w H (t₀ + i * h)) (P i) ∧
        IsWeakPoincare (P i) (muT w H (t₀ + i * h)) A b)
    (T : ℕ) :
    ∃ q : (Fin (m + 1) → Ω) × (Fin (m + 1) → Ω) → ℝ,
      IsCoupling
          (fun x => muT w H t₀ (x 0) *
            ∏ i : Fin m, (P ((i : ℕ) + 1) ^ T) (x i.castSucc) (x i.succ))
          (fun y => ∏ i : Fin (m + 1), muT w H (t₀ + (i : ℕ) * h) (y i)) q ∧
        ∑ p, (if ∃ i, H (p.1 i) ≠ H (p.2 i) then q p else 0) ≤
          (m : ℝ) ^ 2 * (Finset.univ.image H).card *
            (Real.exp (-(T : ℝ) / (2 * A)) + Real.sqrt b) := by sorry

end LowTempGlauber
