-- Prove2me | Theorems.Thm_OgawaNagaoka_eq7_maximizer_condition
-- name    : OgawaNagaoka.eq7_maximizer_condition
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:24:16.429988+00:00
-- url     : https://prove2.me/theorems/94768bdd-d0fa-470e-9dde-458936c6f122
-- title:
--   Eqs. (7)–(8): $\pi^*$ maximizes $f$ iff $\mathrm{Tr}S^{\beta-1}\rho_i^{1/\beta}\le\mathrm{Tr}S^\beta$
-- statement:
--   Let $\rho_1,\dots,\rho_a$ be density operators on a finite-dimensional Hilbert space, $0<\beta\le1$, and $\pi^*$ a probability distribution on the alphabet. Put
--
--   $$
--   S=\sum_{i=1}^a\pi^*_i\rho_i^{1/\beta}.
--   $$
--
--   Then $\pi^*$ attains the maximum of $f(\pi)=\mathrm{Tr}(\sum_i\pi_i\rho_i^{1/\beta})^\beta$ over the probability distributions if and only if, for every $i$,
--
--   $$
--   \mathrm{Tr}\,S^{\beta-1}\rho_i^{1/\beta}\le\mathrm{Tr}\,S^\beta\qquad(\text{equality if }\pi^*_i>0).
--   $$
--
--   When $S$ is singular and $\beta<1$, $\mathrm{Tr}\,S^{\beta-1}\rho_i^{1/\beta}$ is read as $+\infty$ unless the support of $\rho_i$ lies in the support of $S$, and otherwise $S^{\beta-1}$ is taken on the support of $S$. So for $\beta<1$ the condition for $i$ includes $\operatorname{Ker}S\subseteq\operatorname{Ker}\rho_i$. These are the Kuhn–Tucker conditions used to show that the product of maximizers is a maximizer in Lemma 2.
--
--   Differences from the source:
--   - reading: $\mathrm{Tr}\,S^{\beta-1}\rho_i^{1/\beta}$ with $S$ possibly singular (undefined on $\operatorname{Ker}S$ for $\beta<1$) → for $\beta<1$, the clause $\operatorname{Ker}S\subseteq\operatorname{Ker}\rho_i$ (`S.mulVec v = 0 → (ρ i).mulVec v = 0`) and $S^{\beta-1}$ taken on the support of $S$; at $\beta=1$, $S^0=I$ and no clause; reason: the extended-value reading ($+\infty$ off the support) is the one under which the equivalence holds: without the clause $\rho_1=|0\rangle\langle0|$, $\rho_2=|1\rangle\langle1|$, $\beta=1/2$, $\pi^*=(1,0)$ satisfies (7) but $f(1/2,1/2)=\sqrt2>1=f(\pi^*)$
--   - encoding: input alphabet $\mathcal X=\{1,\dots,a\}$, Hilbert space $H$ with $\dim H<\infty$, $H^{\otimes n}$ → finite types `A`, `D`; $H=\mathbb C^D$; $H^{\otimes n}=\mathbb C^{D^n}$ indexed by `Fin n → D`; reason: every finite alphabet and every finite-dimensional Hilbert space is isomorphic to such a model, so the instances are the same
--   - encoding: $\pi^*$ attains the maximum of $f$ over $P_{\mathcal X}$ → `∀ π ∈ stdSimplex ℝ A, traceGallager ρ β π ≤ traceGallager ρ β πs`; reason: definition of a maximizer
--   - encoding: traces $\mathrm{Tr}$ of operators → real part of the matrix trace; reason: the traces involved are traces of products of positive semidefinite operators or of Hermitian operators, which are real
--   - encoding: operator powers $B^p$ → `matPow B p = cfc (x ↦ x ^ p) B` (continuous functional calculus, `Real.rpow`); reason: for a positive semidefinite $B$ and $p>0$ the functional calculus is the definition of $B^p$, with $0^p=0$
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, eqs. (7)–(8), pp.4–5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_OgawaNagaoka_matPow
import Definitions.Def_OgawaNagaoka_traceGallager

open QAlgorithms

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, eqs. (7)–(8), pp.4–5: a probability distribution `π* ∈ P_X` attains the
maximum of `f(π) = Tr (Σ_i π_i ρ_i^{1/β})^β` if and only if, for every `i`,
`Tr S^{β−1} ρ_i^{1/β} ≤ Tr S^β` (equality if `π*_i > 0`), where `S = Σ_{i=1}^a π*_i ρ_i^{1/β}`.

**Formalization Note.** `S` may be singular, and the paper does not say what `S^{β−1}` means on
`Ker S` when `β < 1`. The reading formalized is the extended-value one: `Tr S^{β−1} ρ_i^{1/β}` is
`+∞` unless the support of `ρ_i` lies in the support of `S` (`Ker S ⊆ Ker ρ_i`), and otherwise it is
computed with the power taken on the support of `S` (`matPow`, which sends the eigenvalue `0` to
`0`). Hence for `β < 1` condition (7) includes `Ker S ⊆ Ker ρ_i`. At `β = 1`, `S^0 = I` and no
support condition is imposed. Without the support condition the "if" direction is false
(`ρ₁ = |0⟩⟨0|`, `ρ₂ = |1⟩⟨1|`, `β = 1/2`, `π* = (1, 0)`). Traces are real parts. -/
theorem eq7_maximizer_condition {A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    (ρ : A → Matrix D D ℂ) (hρ : ∀ i, IsDensityMatrix (ρ i)) (β : ℝ) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (πs : A → ℝ) (hπs : πs ∈ stdSimplex ℝ A) :
    let S : Matrix D D ℂ := ∑ i, ((πs i : ℝ) : ℂ) • matPow (ρ i) (1 / β)
    (∀ π ∈ stdSimplex ℝ A, traceGallager ρ β π ≤ traceGallager ρ β πs) ↔
      ∀ i, (β < 1 → ∀ v : D → ℂ, S.mulVec v = 0 → (ρ i).mulVec v = 0) ∧
        (matPow S (β - 1) * matPow (ρ i) (1 / β)).trace.re ≤ (matPow S β).trace.re ∧
        (0 < πs i →
          (matPow S (β - 1) * matPow (ρ i) (1 / β)).trace.re = (matPow S β).trace.re) := by sorry

end OgawaNagaoka
