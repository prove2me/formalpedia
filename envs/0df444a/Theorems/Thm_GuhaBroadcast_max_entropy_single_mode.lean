-- Prove2me | Theorems.Thm_GuhaBroadcast_max_entropy_single_mode
-- name    : GuhaBroadcast.max_entropy_single_mode
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:23:28.93478+00:00
-- url     : https://prove2.me/theorems/0420f17e-8b08-4a82-9df0-1ad5f7782e8d
-- title:
--   Maximum entropy of a single mode with $\langle\hat a^\dagger\hat a\rangle\le N$ is $g(N)$
-- statement:
--   Let $N\ge0$ and $g(x)=(1+x)\log(1+x)-x\log x$ (nats). Then
--
--   1. every single-mode bosonic state $\hat\rho$ with mean photon number $\langle\hat a^\dagger\hat a\rangle\le N$ satisfies $S(\hat\rho)\le g(N)$;
--   2. the thermal state of mean $N$, with photon-number distribution $N^a/(N+1)^{a+1}$, is a state with $\langle\hat a^\dagger\hat a\rangle=N$ and $S=g(N)$.
--
--   So $g(N)$ is the maximum entropy under the photon-number constraint. The paper uses it mode by mode in (16) and for the averaged states in (19) and (24).
--
--   **Formalization Note** Entropy is `spectralEntropyNats` in $[0,\infty]$, the photon number is `modeEnergy`, the thermal state is `identicalThermalKernel 1 N`; at $N=0$ it is the vacuum and $g(0)=0$.
--
--   Differences from the source:
--   - reading: 'the maximum von Neumann entropy ... with ⟨â†â⟩ ≤ N̄ is given by g(N̄)' → an upper bound for every state with mean ≤ N, and attainment by the thermal state of mean N; reason: a maximum has both clauses; naming the maximizer is stronger than bare attainment
--   - encoding: entropy logarithm base unspecified → natural logarithm (nats), entropies in ℝ≥0∞; reason: a change of base scales every term
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section III, before eq. (16), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section III, p.3 (PDF page; the paper prints no page numbers): "the maximum von Neumann
entropy of a single-mode Bosonic state with ⟨â†â⟩ ≤ N̄ is given by g(N̄)", where
`g(x) = (1 + x) log(1 + x) − x log(x)` (p.2).

Both clauses of "maximum": every single-mode state with mean photon number at most `N` has entropy at
most `g(N)`, and the thermal state of mean `N` is a state with mean exactly `N` and entropy `g(N)`.

**Formalization Note.** Entropy is the published `spectralEntropyNats` (nats, in `ℝ≥0∞`), the photon
number is `modeEnergy` of the single mode `0 : Fin 1`, and the thermal state is
`identicalThermalKernel 1 N` (diagonal, weights `N^a/(N+1)^{a+1}`), all from
`QAlgorithms.Papers.Independent.Next46.P32`; `g` is `Claimed50.P39.g` with `g 0 = 0`. `N = 0` is allowed
(the vacuum). -/
theorem max_entropy_single_mode (N : ℝ) (hN : 0 ≤ N) :
    (∀ ρ : State (NumberString 1), modeEnergy ρ.coefficients 0 ≤ ENNReal.ofReal N →
      spectralEntropyNats ρ.coefficients ≤ ENNReal.ofReal (g N)) ∧
    ∃ ρ : State (NumberString 1), ρ.coefficients = identicalThermalKernel 1 N ∧
      modeEnergy ρ.coefficients 0 = ENNReal.ofReal N ∧
      spectralEntropyNats ρ.coefficients = ENNReal.ofReal (g N) := by sorry

end GuhaBroadcast
