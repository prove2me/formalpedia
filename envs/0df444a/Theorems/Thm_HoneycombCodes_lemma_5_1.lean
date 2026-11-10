-- Prove2me | Theorems.Thm_HoneycombCodes_lemma_5_1
-- name    : HoneycombCodes.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:31:05.955706+00:00
-- url     : https://prove2.me/theorems/eaa11104-ac87-4485-b915-0c592eae413e
-- title:
--   Lemma 5.1 — Følner boxes realize $\Gamma_{HC}$ and $\Phi_{HC}$
-- statement:
--   Fix a parameter point $q=(x,\eta,\rho,z)$ in the strict region
--
--   $$
--   0<x<\tfrac12,\qquad 0<\eta,\rho<\tfrac12,\qquad |A-B|<E<A+B, \tag{49}
--   $$
--
--   and let $k_n/n\to z$. There are connected sets of valid triples $\Omega_n$ such that
--
--   $$
--   \liminf_{n\to\infty}\lambda_{max}(J_{\Omega_n})\ge\Gamma_{HC}(q),\qquad \frac1n\log_2\frac{\sum_{\omega\in\Omega_n}D_\omega}{f_{(n-k_n,k_n)}}\longrightarrow\Phi_{HC}(q). \tag{50–51}
--   $$
--
--   This is the continuum limit that turns the finite bound of Theorem 4.8 into the exponent $\kappa_{HC}$.
--
--   **Formalization Note** $k_n$ is a sequence of naturals with $2k_n\le n$; the sets $\Omega_n$ are valid at $(n,k_n)$ and connected for all sufficiently large $n$.
--
--   Differences from the source:
--
--   - reading: lim inf_{n→∞} λ_max(J_{Ω_n}) ≥ Γ_HC(q) → for every ε > 0, eventually λ_max(J_{Ω_n}) ≥ Γ_HC(q) − ε; reason: equivalent definition of the lim inf inequality, avoiding a real lim inf of a possibly unbounded sequence
--   - reading: 'there are connected sets of valid triples Ω_n' → a sequence Ω_n that is valid and connected for all sufficiently large n; reason: only large n matter for (50)–(51); the proof constructs the boxes 'for all sufficiently large n'
--   - encoding: k_n with k_n/n → z (stabilizer type (n − k_n, k_n)) → kseq : ℕ → ℕ with 2·kseq n ≤ n and kseq n / n → z; reason: (n − k_n, k_n) is a partition exactly when 2k_n ≤ n
--   - reading: contraction coefficients p_{ω,ω′} 'using Theorem 4.4' (squared 6j symbols, Racah factor R²_{στ}) → the closed forms (32)–(33) with R²_{σσ} = Q_σ, R²_{σ,1−σ} = 1 − Q_σ from Remark 4.7 and (117), set to 0 when an endpoint is not valid; reason: Remark 4.7 and App. A.2 identify the squared Racah factors with this closed form, which is what the paper computes with
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §5.1, Lemma 5.1, eqs. (49)–(51), p.25 (PDF 27)

import Mathlib
import Definitions.Def_HoneycombCodes_pDir
import Definitions.Def_HoneycombCodes_lamProfile
import Definitions.Def_BlockBochner_lamMax
import Definitions.Def_HoneycombCodes_kappaHC

set_option autoImplicit false

open Filter Topology

namespace HoneycombCodes

/-- **Lemma 5.1**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), p.25 (PDF 27). Fix `q = (x, η, ρ, z)` in the strict region (49)
`0 < x < 1/2`, `0 < η, ρ < 1/2`, `|A − B| < E < A + B`, and let `k_n/n → z`. There are connected
sets of valid triples `Ω_n` such that `lim inf_{n→∞} λ_max(J_{Ω_n}) ≥ Γ_HC(q)` (50) and
`(1/n) log₂(Σ_{ω ∈ Ω_n} D_ω / f_{(n−k_n, k_n)}) → Φ_HC(q)` (51).

**Formalization Note.** `k_n` is a sequence of naturals with `2k_n ≤ n` (the stabilizer type
`(n − k_n, k_n)` is a partition); `Ω_n` is a `Finset` of triples, valid at `(n, k_n)` and connected
in the positive-weight box-transfer graph for all large `n`. The `lim inf` bound (50) is: for every
`ε > 0`, eventually `λ_max(J_{Ω_n}) ≥ Γ_HC(q) − ε`. (51) is a `Tendsto` with `log₂ = Real.logb 2`
and `f_{(n−k, k)} = specht2 n k`. -/
theorem lemma_5_1 (x η ρ z : ℝ) (hq : InStrictHC x η ρ z)
    (kseq : ℕ → ℕ) (hk : ∀ n, 2 * kseq n ≤ n)
    (hkz : Tendsto (fun n : ℕ => (kseq n : ℝ) / n) atTop (𝓝 z)) :
    ∃ Ωs : ℕ → Finset (ℕ × ℕ × ℕ),
      (∀ᶠ n in atTop, (∀ ω ∈ Ωs n, IsValidTriple n (kseq n) ω) ∧
        IsConnectedOmega n (kseq n) (Ωs n)) ∧
      (∀ ε > 0, ∀ᶠ n in atTop, GammaHC x η ρ z - ε ≤ BlockBochner.lamMax (JOmega n (kseq n) (Ωs n))) ∧
      Tendsto (fun n : ℕ =>
          Real.logb 2 ((∑ ω ∈ Ωs n, Domega n ω) / specht2 n (kseq n)) / n)
        atTop (𝓝 (PhiHC x η ρ z)) := by sorry

end HoneycombCodes
