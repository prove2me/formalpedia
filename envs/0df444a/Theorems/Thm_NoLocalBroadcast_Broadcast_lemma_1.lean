-- Prove2me | Theorems.Thm_NoLocalBroadcast_Broadcast_lemma_1
-- name    : NoLocalBroadcast.Broadcast.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:16.484629+00:00
-- url     : https://prove2.me/theorems/269ce9a0-51e1-4d0b-85da-f720b59aef1d
-- title:
--   Lemma 1 (p. 2) (corrected: commutation of the σ_i with p_i > 0) — for a CQ state I = I_CQ = χ, and I = I_CC iff the σ_i commute iff ρ is CC; with the QC mirror
-- statement:
--   Let $A$, $B$ be finite-dimensional systems.
--
--   **CQ states.** Let $\{|i\rangle\}_{i=1}^k$ be an orthonormal family of $A$, $\{p_i\}$ a probability distribution, $\sigma_i$ states of $B$, and
--
--   $$\rho=\sum_ip_i\,|i\rangle\langle i|\otimes\sigma_i .$$
--
--   Then
--
--   1. $I(\rho)=I_{CQ}(\rho)$;
--   2. $I(\rho)=\chi(\{p_i,\sigma_i\})=S\big(\sum_ip_i\sigma_i\big)-\sum_ip_iS(\sigma_i)$;
--   3. $I(\rho)=I_{CC}(\rho)$ if and only if $\sigma_i\sigma_j=\sigma_j\sigma_i$ for all $i,j$ with $p_i>0$ and $p_j>0$;
--   4. $I(\rho)=I_{CC}(\rho)$ if and only if $\rho$ is classical-classical.
--
--   **QC states.** Let $\{|i\rangle\}_{i=1}^k$ be an orthonormal family of $B$, $\{p_i\}$ a probability distribution, $\sigma_i$ states of $A$, and $\rho=\sum_ip_i\,\sigma_i\otimes|i\rangle\langle i|$. Then $I(\rho)=\chi(\{p_i,\sigma_i\})$, and $I(\rho)=I_{CC}(\rho)$ holds if and only if $\sigma_i\sigma_j=\sigma_j\sigma_i$ for all $i,j$ with $p_i,p_j>0$, if and only if $\rho$ is classical-classical.
--
--   Clauses 3 and 4 together give the printed "$I(\rho)=I_{CC}(\rho)$ if and only if the states $\sigma_i$ commute and $\rho$ is CC", with commutation required only of the states that occur with positive probability. The QC half is the same lemma with the two parties exchanged; the proof of Theorem 1 applies it to a QC state.
--
--   **Formalization Note** Orthonormal families are indexed by `Fin k` and need not be bases; $p_i$ may vanish.
--
--   Differences from the source:
--   - correction: I(ρ) = I_CC(ρ) iff the states σ_i^B commute and ρ is CC → commutation required only of σ_i, σ_j with p_i > 0 and p_j > 0; reason: as printed the statement is false: A = B = ℂ², p = (1, 0), σ_0 = |0⟩⟨0|, σ_1 = |+⟩⟨+| gives ρ = |0⟩⟨0| ⊗ |0⟩⟨0|, a CC product state with I = I_CC = 0, but σ_0σ_1 ≠ σ_1σ_0
--   - generalization: one iff: I = I_CC ⟺ (the σ_i commute ∧ ρ is CC) → two iffs: I = I_CC ⟺ the σ_i (p_i > 0) commute, and I = I_CC ⟺ ρ is CC; reason: the two iffs together imply the (corrected) printed iff
--   - generalization: CQ states Σ_i p_i |i⟩⟨i| ⊗ σ_i^B only → also QC states Σ_i p_i σ_i ⊗ |i⟩⟨i| (I = χ and both I = I_CC iffs); reason: the mirror is the same lemma with the parties exchanged, used for a QC state in the proof of Theorem 1; the CQ half is the source's statement
--   - encoding: orthonormal set {|i⟩} → Orthonormal family e : Fin k → EuclideanSpace ℂ a; reason: an orthonormal set is a finite orthonormal family in finite dimension
--   - encoding: finite-dimensional systems A, B and quantum states → nonempty finite index types a, b; states are positive semidefinite trace-one matrices (QAlgorithms.IsDensityMatrix), A the first factor of a × b; reason: the paper works in finite dimension throughout; same instances
--   - encoding: I_CQ, I_CC as maxima over measurement maps with an orthonormal register → sSup over POVMs with any finite number n of outcomes, the outcome written in the computational basis of Fin n; reason: the maximum is attained in finite dimension, so sSup is the paper's value; any other orthonormal register gives a unitarily equivalent state with the same entropies
--   - encoding: log of unspecified base in S(ρ) = −Tr ρ log ρ → QAlgorithms.vnEntropy, base 2; reason: every statement here is invariant under the base of the logarithm
-- source:
--   Piani, Horodecki & Horodecki, No-local-broadcasting theorem for quantum correlations, arXiv:0707.0848v2, p. 2, Lemma 1

import Mathlib
import Definitions.Def_NoLocalBroadcast_Broadcast_Model

namespace NoLocalBroadcast.Broadcast

open Matrix
open scoped Kronecker

/-- Lemma 1, p. 2 (corrected: commutation only of the `σ_i` with `p_i > 0`), with its mirror for
QC states. For a CQ state `ρ = Σ_i p_i |i⟩⟨i| ⊗ σ_i`: `I(ρ) = I_CQ(ρ)`, `I(ρ) = χ({p_i, σ_i})`,
and `I(ρ) = I_CC(ρ)` iff the `σ_i` with `p_i > 0` commute, iff `ρ` is CC. For a QC state
`ρ = Σ_i p_i σ_i ⊗ |i⟩⟨i|`: `I(ρ) = χ({p_i, σ_i})`, and `I(ρ) = I_CC(ρ)` iff the `σ_i` with
`p_i > 0` commute, iff `ρ` is CC. -/
theorem lemma_1 {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b] :
    (∀ (k : ℕ) (e : Fin k → EuclideanSpace ℂ a) (p : Fin k → ℝ) (σ : Fin k → Matrix b b ℂ),
      Orthonormal ℂ e → (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
      (∀ i, QAlgorithms.IsDensityMatrix (σ i)) →
      ∀ ρ : Matrix (a × b) (a × b) ℂ,
        ρ = ∑ i, (p i : ℂ) • (QAlgorithms.pureDensity (e i) ⊗ₖ σ i) →
        mutualInfo ρ = I_CQ ρ ∧ mutualInfo ρ = holevoChi p σ ∧
        (mutualInfo ρ = I_CC ρ ↔ ∀ i j, 0 < p i → 0 < p j → σ i * σ j = σ j * σ i) ∧
        (mutualInfo ρ = I_CC ρ ↔ IsClassicalClassical ρ)) ∧
    (∀ (k : ℕ) (e : Fin k → EuclideanSpace ℂ b) (p : Fin k → ℝ) (σ : Fin k → Matrix a a ℂ),
      Orthonormal ℂ e → (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
      (∀ i, QAlgorithms.IsDensityMatrix (σ i)) →
      ∀ ρ : Matrix (a × b) (a × b) ℂ,
        ρ = ∑ i, (p i : ℂ) • (σ i ⊗ₖ QAlgorithms.pureDensity (e i)) →
        mutualInfo ρ = holevoChi p σ ∧
        (mutualInfo ρ = I_CC ρ ↔ ∀ i j, 0 < p i → 0 < p j → σ i * σ j = σ j * σ i) ∧
        (mutualInfo ρ = I_CC ρ ↔ IsClassicalClassical ρ)) := by sorry

end NoLocalBroadcast.Broadcast
