-- Prove2me | Theorems.Thm_GapAgnosticGS_lemma_3_1
-- name    : GapAgnosticGS.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:32:54.969221+00:00
-- url     : https://prove2.me/theorems/9484a0f5-827f-4eda-8500-279dd12ddcd5
-- title:
--   Lemma 3.1 — a Hamiltonian as a hidden-basis bandit whose best arm is the ground state
-- statement:
--   Let $H$ be a Hermitian $n\times n$ matrix with all eigenvalues in $[-\alpha,\alpha]$, $\alpha>0$, and let $\{|\phi_j\rangle\}$ be any orthonormal eigenbasis, $H|\phi_j\rangle=E_j|\phi_j\rangle$ with $E_0\le\dots\le E_{n-1}$. Let $W_H=e^{i\pi H/(4\alpha)}$, $\vartheta_j=\frac\pi2\big(1+\frac{E_j}{2\alpha}\big)$ and
--
--   $$|\mathrm{arm}_j\rangle=\frac{1+e^{i\vartheta_j}}{2}|0\rangle+\frac{1-e^{i\vartheta_j}}{2}|1\rangle .$$
--
--   Then:
--
--   1. $\mathcal E_H=(I\otimes\mathrm{Had})(I\otimes S)(\text{ctrl-}W_H)(I\otimes\mathrm{Had})$ is a hidden-basis environment with one arm qubit, $|0\rangle_A$, reward projector $\Pi=|0\rangle\langle0|$, hidden basis $\{|\phi_j\rangle\}$ and arm states $|\mathrm{arm}_j\rangle$;
--   2. $p_j=\cos^2(\vartheta_j/2)$;
--   3. rewards strictly decrease with energy, and $p_j=p_\star$ exactly when $E_j=E_0$ (the best arms are the ground states);
--   4. for every $j$,
--   $$\frac{\pi}{8\sqrt2\,\alpha}(E_j-E_0)\le p_\star-p_j\le\frac{\pi}{8\alpha}(E_j-E_0);$$
--   5. controlled-$\mathcal E_H$ and controlled-$\mathcal E_H^\dagger$ can each be implemented with one controlled query to $W_H$ (resp. $W_H^\dagger$): there are oracle-free unitaries $V_1,V_2$ on the system plus one extra qubit such that, for every unitary $W$, $V_2\,(\text{ctrl-}W\otimes I)\,V_1$ acts as controlled-$\mathcal E(W)$ (resp. with $W^\dagger$, as controlled-$\mathcal E(W)^\dagger$) with the extra qubit starting and ending in $|0\rangle$.
--
--   This lemma reduces ground-state preparation to best-arm identification in the hidden-basis bandit, preserving energy gaps up to the factor $\pi/(8\alpha)$.
--
--   Differences from the source:
--   - encoding: ‖H‖ ≤ α → H Hermitian with every eigenvalue in [−α, α]; reason: the spectral norm of a Hermitian matrix is its largest eigenvalue modulus; p.1 writes the assumption as spec(H) ⊆ [−α, α]
--   - generalization: reward gaps c(E_j−E_0)/α ≤ p⋆ − p_j ≤ C(E_j−E_0)/α for universal constants c, C → the explicit constants c = π/(8√2), C = π/8, and the proof's explicit arm states and p_j = cos²(ϑ_j/2) as additional clauses; reason: these are the values computed in the proof (p.9); forgetting them gives the printed statement
--   - reading: the arms are the eigenstates of H with the best arm being the ground state → for every orthonormal eigenbasis, the environment with that hidden basis; rewards strictly decrease in energy and p_j = p⋆ iff E_j = E_0; reason: a degenerate excited level has many eigenbases; the claim holds for each
--   - reading: Controlled versions of E_H and E_H† can each be implemented with one controlled query to W_H and its inverse → oracle-free unitaries V₁, V₂ (chosen before W) with V₂(ctrl-W ⊗ 1)V₁ = ctrl-E(W) (resp. ctrl-W†, ctrl-E(W)†) on one extra qubit returned to |0⟩, for every unitary W; reason: 'implemented with one query' means the rest of the circuit does not depend on the oracle; W = W_H is the printed case
--   - encoding: arms j ∈ {1, …, n} → 0-based indices j : Fin n; reason: Lean convention; same arms
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.1 and its proof, pp.8–9 (PDF pp.9–10)

import Definitions.Def_GapAgnosticGS_energy
import Definitions.Def_GapAgnosticGS_phaseOracle
import Definitions.Def_GapAgnosticGS_envH
import Definitions.Def_GapAgnosticGS_pStar
open QAlgorithms

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.1, p.8 (PDF p.9), with its proof, pp.8–9 (PDF pp.9–10): "For any Hamiltonian H
with ‖H‖ ≤ α, there is a HidQMAB environment E_H using one ancilla qubit and one controlled query
to W_H = e^{iτH} with τ = π/(4α) such that the arms are the eigenstates of H with the best arm
being the ground state, and with reward gaps c(E_j−E_0)/α ≤ p⋆ − p_j ≤ C(E_j−E_0)/α for universal
constants c and C, hence preserving the energy gaps. Controlled versions of E_H and E_H† can each
be implemented with one controlled query to W_H and its inverse."

For Hermitian `H` with all eigenvalues in `[−α, α]` and any orthonormal eigenbasis `ϕ`
(`H ϕ_j = E_j ϕ_j`), with `ϑ_j = (π/2)(1 + E_j/(2α))` and
`|arm_j⟩ = ((1 + e^{iϑ_j})/2)|0⟩ + ((1 − e^{iϑ_j})/2)|1⟩`:
1. `E_H = envH W_H` is a hidden-basis environment with arm register one qubit, `|0⟩_A`, reward
   projector `Π = |0⟩⟨0|`, hidden basis `ϕ` and arms `arm_j`;
2. `p_j = cos²(ϑ_j/2)`;
3. rewards strictly decrease with energy, and the best arms are exactly the ground eigenvectors;
4. `π/(8√2 α)·(E_j − E_0) ≤ p⋆ − p_j ≤ π/(8α)·(E_j − E_0)`;
5. controlled-`E_H` and controlled-`E_H†` are each, for every unitary `W` on `ℂⁿ`, an
   oracle-free unitary, one controlled `W` (resp. `W†`) query on one extra qubit, and an
   oracle-free unitary, with the extra qubit returned to `|0⟩`.

**Formalization Note.** "‖H‖ ≤ α" is `|E_j| ≤ α` for every eigenvalue (the spectral norm of a
Hermitian matrix is its largest eigenvalue modulus; p.1 writes it `spec(H) ⊆ [−α, α]`). The
universal constants are the proof's explicit `c = π/(8√2)`, `C = π/8`. Clause 5 states
"implemented with one controlled query" as an oracle-independent circuit (`V₁`, `V₂` chosen
before `W`), on the register `(anc, I) × (control, A)`. -/
theorem lemma_3_1 {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (α : ℝ)
    (hα : 0 < α) (hnorm : ∀ j, |energy H j| ≤ α)
    (ϕ : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hϕ : ∀ j, act H (ϕ j) = (energy H j : ℂ) • ϕ j) :
    let Pi0 : Matrix Bool Bool ℂ := Matrix.single false false 1
    let ϑ : Fin n → ℝ := fun j => Real.pi / 2 * (1 + energy H j / (2 * α))
    let armH : Fin n → EuclideanSpace ℂ Bool := fun j => WithLp.toLp 2 fun b =>
      if b then (1 - Complex.exp ((ϑ j : ℂ) * Complex.I)) / 2
      else (1 + Complex.exp ((ϑ j : ℂ) * Complex.I)) / 2
    let emb : EuclideanSpace ℂ (Bool × (Fin n × Bool)) →
        EuclideanSpace ℂ ((Bool × Fin n) × (Bool × Bool)) := fun v =>
      WithLp.toLp 2 fun x => if x.1.1 = false then v (x.2.1, (x.1.2, x.2.2)) else 0
    (∃ Env : HidEnv n Bool false Pi0,
      Env.E = envH (phaseOracle H α) ∧ (∀ j, Env.φ j = ϕ j) ∧ (∀ j, Env.arm j = armH j) ∧
      (∀ j, reward Env j = Real.cos (ϑ j / 2) ^ 2) ∧
      (∀ j k, energy H j < energy H k → reward Env k < reward Env j) ∧
      (∀ j, reward Env j = pStar Env ↔ energy H j = minEigenvalue H) ∧
      (∀ j, Real.pi / (8 * Real.sqrt 2 * α) * (energy H j - minEigenvalue H) ≤
          pStar Env - reward Env j ∧
        pStar Env - reward Env j ≤ Real.pi / (8 * α) * (energy H j - minEigenvalue H))) ∧
    (∃ V₁ V₂ : Matrix ((Bool × Fin n) × (Bool × Bool)) ((Bool × Fin n) × (Bool × Bool)) ℂ,
      V₁ ∈ Matrix.unitaryGroup _ ℂ ∧ V₂ ∈ Matrix.unitaryGroup _ ℂ ∧
      ∀ W ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ v,
        act (V₂ * Matrix.kronecker (controlled W) (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) * V₁)
            (emb v) = emb (act (controlled (envH W)) v)) ∧
    (∃ V₁ V₂ : Matrix ((Bool × Fin n) × (Bool × Bool)) ((Bool × Fin n) × (Bool × Bool)) ℂ,
      V₁ ∈ Matrix.unitaryGroup _ ℂ ∧ V₂ ∈ Matrix.unitaryGroup _ ℂ ∧
      ∀ W ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ v,
        act (V₂ * Matrix.kronecker (controlled W.conjTranspose)
              (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) * V₁) (emb v) =
          emb (act (controlled (envH W).conjTranspose) v)) := by sorry

end GapAgnosticGS
