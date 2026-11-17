-- Prove2me | Theorems.Thm_GaussTesting_Supplement_theorem_9_3
-- name    : GaussTesting.Supplement.theorem_9_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:28:35.487976+00:00
-- url     : https://prove2.me/theorems/8eb18c6f-2ec3-4a67-a5a2-68d82d202bd8
-- title:
--   Theorem 9.3 — lower bound master theorem: distinguishing the hard pair needs $N\ge\log(1/\delta)/(20(\varepsilon_B-\varepsilon_A)^2)$ copies
-- statement:
--   Let $\mathcal C$ be a class of pure states (unit vectors) in a Hilbert space $\mathcal H=\ell^2(\iota)$, and suppose that there are orthonormal states $|A\rangle,|B\rangle$ with $|A\rangle\in\mathcal C$ and
--
--   $$
--   |\langle A|\phi\rangle|+|\langle B|\phi\rangle|\le1\qquad\text{for every }|\phi\rangle\in\mathcal C\qquad(9.4)
--   $$
--
--   (the premise of Lemma 9.2). Let $0\le\varepsilon_A<\varepsilon_B\le1/\sqrt2$ and $0<\delta\le1/4$. Then there are pure states $|\psi_A\rangle,|\psi_B\rangle$ with
--
--   $$
--   \mathrm{dist}(\psi_A,\mathcal C)\le\varepsilon_A,\qquad\mathrm{dist}(\psi_B,\mathcal C)\ge\varepsilon_B\qquad(9.8)
--   $$
--
--   such that every quantum algorithm which distinguishes them with probability at least $1-\delta$ consumes
--
--   $$
--   N\ \ge\ \frac{\log(1/\delta)}{20\,(\varepsilon_B-\varepsilon_A)^2}\qquad(9.9)
--   $$
--
--   copies of the unknown state. An algorithm on $N$ copies is a two-outcome measurement $\{M,I-M\}$ on $\mathcal H^{\otimes N}$, $0\preceq M\preceq I$, outputting "$\psi_A$" on $M$; distinguishing with probability $1-\delta$ means $\langle\psi_A^{\otimes N}|M|\psi_A^{\otimes N}\rangle\ge1-\delta$ and $\langle\psi_B^{\otimes N}|M|\psi_B^{\otimes N}\rangle\le\delta$.
--
--   Any $(\varepsilon_A,\varepsilon_B,\delta)$-tester for $\mathcal C$ distinguishes $\psi_A$ from $\psi_B$, so this reduces testing lower bounds for a class to exhibiting one pair $|A\rangle,|B\rangle$; it is the engine behind Theorem 1.6.
--
--   **Formalization Note** The pair $\psi_A,\psi_B$ is chosen before $N$ and $M$. $\log$ is the natural logarithm, the constant is exactly $20$, and $N$ ranges over all natural numbers.
--
--   Differences from the source:
--   - encoding: 'the states |A⟩, |B⟩ of Lemma 9.2 exist for the class 𝒞' → hypotheses ‖A‖ = ‖B‖ = 1, ⟪A, B⟫ = 0, A ∈ 𝒞 and ‖⟪A, ϕ⟫‖ + ‖⟪B, ϕ⟫‖ ≤ 1 for all ϕ ∈ 𝒞 (eq. (9.4)); reason: this is Lemma 9.2's premise written out
--   - encoding: any quantum algorithm which can distinguish these two states with probability at least 1 − δ, consuming N copies → every N and every effect M on ℋ^{⊗N} with Re⟨ψ_A^{⊗N}, M ψ_A^{⊗N}⟩ ≥ 1 − δ and Re⟨ψ_B^{⊗N}, M ψ_B^{⊗N}⟩ ≤ δ; reason: the paper's own reading in the proof of Proposition 9.1, eq. (9.2): a POVM {M, I − M} on N copies
--   - encoding: Hilbert space ℋ, class of pure states → ℓ²(ι) for an arbitrary index type ι; 𝒞 a set of unit vectors; reason: every Hilbert space with an orthonormal basis indexed by ι is ℓ²(ι)
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Theorem 9.3, p.76; Lemma 9.2, eq. (9.4), p.75; Proposition 9.1, eq. (9.2), p.75

import Definitions.Def_GaussTesting_Supplement_IsCopyTester

namespace GaussTesting

namespace Supplement

/-- **Theorem 9.3 (Lower bound master theorem).** Let `𝒞` be a class of pure states,
`0 ≤ ε_A < ε_B ≤ 1/√2` and `0 < δ ≤ 1/4`. Suppose that orthonormal states `|A⟩, |B⟩` with `|A⟩ ∈ 𝒞` and
`|⟨A|ϕ⟩| + |⟨B|ϕ⟩| ≤ 1` for every `|ϕ⟩ ∈ 𝒞` exist (the premise of Lemma 9.2, eq. (9.4)). Then there are
states `|ψ_A⟩, |ψ_B⟩` with `dist(ψ_A, 𝒞) ≤ ε_A` and `dist(ψ_B, 𝒞) ≥ ε_B` (9.8) such that every quantum
algorithm that distinguishes them with probability at least `1 − δ` consumes
`N ≥ log(1/δ) / (20 (ε_B − ε_A)²)` copies (9.9).

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian
states*, arXiv:2609.39113 (sha256 6683e57b…), Theorem 9.3, p.76; Lemma 9.2, eq. (9.4), p.75; proof of
Proposition 9.1, eq. (9.2), p.75.

**Formalization Note.**
* A distinguishing algorithm on `N` copies is a two-outcome POVM `{M, I − M}` on `ℋ^{⊗N}` (outcome `M` =
  "the state is `ψ_A`") with `tr(M ψ_A^{⊗N}) ≥ 1 − δ` and `tr(M ψ_B^{⊗N}) ≤ δ`, as in eq. (9.2).
* `ψ_A, ψ_B` are chosen before `N` and `M`; `log` is the natural logarithm; `N` ranges over all naturals.
* `⟪A, B⟫ = 0` with unit norms is "orthonormal"; `‖⟪A, ϕ⟫‖ = |⟨A|ϕ⟩|`. -/
theorem theorem_9_3 {ι : Type*} (C : Set (Ell2 ι)) (hC : ∀ φ ∈ C, ‖φ‖ = 1)
    (A B : Ell2 ι) (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hAB : inner ℂ A B = 0) (hAC : A ∈ C)
    (hpair : ∀ φ ∈ C, ‖inner ℂ A φ‖ + ‖inner ℂ B φ‖ ≤ 1)
    (εA εB δ : ℝ) (hεA : 0 ≤ εA) (hεAB : εA < εB) (hεB : εB ≤ 1 / Real.sqrt 2)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) :
    ∃ ψA ψB : Ell2 ι, ‖ψA‖ = 1 ∧ ‖ψB‖ = 1 ∧ distTo ψA C ≤ εA ∧ εB ≤ distTo ψB C ∧
      ∀ (N : ℕ) (M : Ell2 (Fin N → ι) →L[ℂ] Ell2 (Fin N → ι)), M.IsPositive → (1 - M).IsPositive →
        1 - δ ≤ copyAccept M ψA → copyAccept M ψB ≤ δ →
        Real.log (1 / δ) / (20 * (εB - εA) ^ 2) ≤ N := by sorry

end Supplement

end GaussTesting
