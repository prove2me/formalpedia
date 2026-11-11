-- Prove2me | Theorems.Thm_GapAgnosticGS_lemma_3_3
-- name    : GapAgnosticGS.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:29:11.821124+00:00
-- url     : https://prove2.me/theorems/83da4988-31be-4195-ad8b-8e9808645476
-- title:
--   Lemma 3.3 — the maximally entangled state is uniform in every hidden basis
-- statement:
--   Let $\{|i\rangle\}_{i=0}^{n-1}$ be the computational basis of $\mathcal H_I=\mathbb C^n$, let $R$ be a reference register of dimension at least $n$ with basis states $|i\rangle_R$ for $i<n$, and let
--
--   $$|\Phi\rangle_{RI}=\frac1{\sqrt n}\sum_{i}|i\rangle_R|i\rangle_I .$$
--
--   Then for every orthonormal basis $\{|\phi_j\rangle\}$ of $\mathcal H_I$,
--
--   $$|\Phi\rangle_{RI}=\frac1{\sqrt n}\sum_{j}|\phi_j^*\rangle_R|\phi_j\rangle_I ,$$
--
--   where $|\phi_j^*\rangle=\sum_i\overline{\langle i|\phi_j\rangle}\,|i\rangle$ is the complex conjugate in the known basis.
--
--   This is the basis-free initialization of the algorithm: without knowing the eigenbasis of $H$, it gives every hidden eigenstate the same weight $1/n$.
--
--   Differences from the source:
--   - encoding: a reference Hilbert space H_R with dimensionality at least n → any finite basis set R with an injection e : Fin n ↪ R, |i⟩_R = |e i⟩; reason: the same register
--   - encoding: indices i, j ∈ [n] = {1, …, n} → 0-based indices Fin n; reason: Lean convention; same sums
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.3 (Uniform superposition in hidden basis), p.9 (PDF p.10)

import Definitions.Def_QAlgorithms_Defs_Hamiltonian
open QAlgorithms

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.3 (Uniform superposition in hidden basis), p.9 (PDF p.10): "Let {|i⟩, i ∈ [n]}
be a known basis of an n-dimensional Hilbert space H_I and |Φ⟩_RI := (1/√n) Σ_{i=1}^n |i⟩_R|i⟩_I
be the maximally entangled state on H_R ⊗ H_I, where H_R is a reference Hilbert space with
dimensionality at least n. Then for every orthonormal basis {|ϕ_j⟩, j ∈ [n]} of H_I, we have
|Φ⟩_RI = (1/√n) Σ_{j=1}^n |ϕ_j^*⟩_R|ϕ_j⟩_I, where complex conjugation is taken in the known
basis {|i⟩, i ∈ [n]}."

**Formalization Note.** `H_I = ℂⁿ` with its computational basis; the reference register is any
finite basis set `R` with an injection `e : Fin n ↪ R` ("dimensionality at least n"; `|i⟩_R` is
`|e i⟩`); `|ϕ_j^*⟩_R = Σ_i conj(⟨i|ϕ_j⟩)|e i⟩`. Indices are 0-based. -/
theorem lemma_3_3 {n : ℕ} {R : Type} [Fintype R] [DecidableEq R] (e : Fin n ↪ R)
    (ϕ : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) :
    let ϕconj : Fin n → EuclideanSpace ℂ R := fun j =>
      ∑ i : Fin n, (starRingEnd ℂ) (ϕ j i) • ket (e i)
    ((Real.sqrt n)⁻¹ : ℂ) • ∑ i : Fin n, tensorVec (ket (e i)) (ket i) =
      ((Real.sqrt n)⁻¹ : ℂ) • ∑ j : Fin n, tensorVec (ϕconj j) (ϕ j) := by sorry

end GapAgnosticGS
