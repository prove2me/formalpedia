-- Prove2me | Theorems.Thm_OgawaNagaoka_lemma3_E0_properties
-- name    : OgawaNagaoka.lemma3_E0_properties
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:26:16.043212+00:00
-- url     : https://prove2.me/theorems/912dac77-a822-411f-b60d-89700af38d71
-- title:
--   Lemma 3: $E_0(0,\pi)=0$, $E_0\le0$, $\partial_sE_0\ge0$, $\partial_sE_0|_{s=0}=I(\pi)$
-- statement:
--   Let $\rho_1,\dots,\rho_a$ be density operators on a finite-dimensional Hilbert space and $\pi$ a probability distribution on the alphabet. Then
--
--   1. $E_0(0,\pi)=0$; (13)
--   2. $E_0(s,\pi)\le0$ for $-1<s\le0$; (14)
--   3. $\dfrac{\partial E_0(s,\pi)}{\partial s}\ge0$ for $-1<s\le0$; (15)
--   4. $\dfrac{\partial E_0(s,\pi)}{\partial s}\Big|_{s=0}=I(\pi)$. (16)
--
--   Together these describe the graph of $s\mapsto E_0(s,\pi)$ near $0$: it passes through the origin with slope $I(\pi)$, which is what makes the exponent of Theorem 1 positive when $R>C$.
--
--   Differences from the source:
--   - encoding: input alphabet $\mathcal X=\{1,\dots,a\}$, Hilbert space $H$ with $\dim H<\infty$, $H^{\otimes n}$ → finite types `A`, `D`; $H=\mathbb C^D$; $H^{\otimes n}=\mathbb C^{D^n}$ indexed by `Fin n → D`; reason: every finite alphabet and every finite-dimensional Hilbert space is isomorphic to such a model, so the instances are the same
--   - reading: $\pi$ (not specified in the statement) → `π ∈ stdSimplex ℝ A`; reason: $E_0(s,\pi)$ is defined for $\pi\in P_{\mathcal X}$ in (11)–(12)
--   - encoding: $\partial E_0/\partial s\ge0$ and $\partial E_0/\partial s|_{s=0}=I(\pi)$ → `HasDerivAt (fun s => E0 ρ s π) d s` with `0 ≤ d`, and `HasDerivAt … (holevoInfo ρ π) 0`; reason: the source's derivatives are asserted to exist; `HasDerivAt` states existence and value, two-sided since $E_0$ is defined for $s>-1$
--   - encoding: $\log$, $H(\rho)=-\mathrm{Tr}\rho\log\rho$ → natural logarithm (`Real.log`; the published `ProjectiveMeasurementEquilibration.vonNeumannEntropy`); reason: the paper's logarithms are natural ($R=\log M/n$ with $M=e^{nR}$)
--   - encoding: traces $\mathrm{Tr}$ of operators → real part of the matrix trace; reason: the traces involved are traces of products of positive semidefinite operators or of Hermitian operators, which are real
--   - encoding: operator powers $B^p$ → `matPow B p = cfc (x ↦ x ^ p) B` (continuous functional calculus, `Real.rpow`); reason: for a positive semidefinite $B$ and $p>0$ the functional calculus is the definition of $B^p$, with $0^p=0$
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, Lemma 3, eqs. (13)–(16), p.7

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_OgawaNagaoka_holevoInfo
import Definitions.Def_OgawaNagaoka_E0

open QAlgorithms

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, Lemma 3, eqs. (13)–(16), p.7: for every probability distribution `π`,
`E₀(0, π) = 0` (13); `E₀(s, π) ≤ 0` for `−1 < s ≤ 0` (14); `∂E₀(s, π)/∂s ≥ 0` for `−1 < s ≤ 0`
(15); `∂E₀(s, π)/∂s |_{s=0} = I(π)` (16).

**Formalization Note.** (15) and (16) are stated with `HasDerivAt`, so they assert that
`s ↦ E₀(s, π)` is differentiable at the point (two-sided; `E₀` is defined on `s > −1`). `I(π)` is
`holevoInfo`, in nats. -/
theorem lemma3_E0_properties {A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    (ρ : A → Matrix D D ℂ) (hρ : ∀ i, IsDensityMatrix (ρ i)) (π : A → ℝ)
    (hπ : π ∈ stdSimplex ℝ A) :
    E0 ρ 0 π = 0 ∧
      (∀ s ∈ Set.Ioc (-1 : ℝ) 0, E0 ρ s π ≤ 0) ∧
      (∀ s ∈ Set.Ioc (-1 : ℝ) 0, ∃ d, HasDerivAt (fun s => E0 ρ s π) d s ∧ 0 ≤ d) ∧
      HasDerivAt (fun s => E0 ρ s π) (holevoInfo ρ π) 0 := by sorry

end OgawaNagaoka
