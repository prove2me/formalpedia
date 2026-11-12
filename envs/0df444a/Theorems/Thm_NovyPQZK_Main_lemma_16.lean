-- Prove2me | Theorems.Thm_NovyPQZK_Main_lemma_16
-- name    : NovyPQZK.Main.lemma_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:35:53.534079+00:00
-- url     : https://prove2.me/theorems/5fb6470d-6579-4ce4-825f-3ff781411e19
-- title:
--   Lemma 16 — Watrous's quantum rewinding lemma, exact case
-- statement:
--   Let $V$ be a register of $a$ qubits and $K$ one of $k$ qubits, $Q$ a unitary on $VK$, and $\{|1\rangle\langle1|\otimes1,\ |0\rangle\langle0|\otimes1\}$ the computational-basis measurement of the first qubit of $VK$. For a unit vector $|\psi\rangle_V$ and $b\in\{0,1\}$ put
--
--   $$p_b(\psi)=\big\|(|b\rangle\langle b|\otimes1)\,Q\,(|\psi\rangle_V|0\rangle_K)\big\|^2,\qquad |\psi(b)\rangle=\frac{(|b\rangle\langle b|\otimes1)\,Q\,(|\psi\rangle_V|0\rangle_K)}{\sqrt{p_b(\psi)}}.$$
--
--   If $p_0(\psi)=p_1(\psi)=\tfrac12$ for every input $|\psi\rangle_V$, then the unitary $U_{\mathrm{Wat}} = Q\,(1_V\otimes(2|0\rangle\langle0|_K-1_K))\,Q^*$ satisfies
--
--   $$|\psi(1)\rangle = U_{\mathrm{Wat}}\,|\psi(0)\rangle\qquad\text{for every state }|\psi\rangle_V.$$
--
--   The zero-knowledge simulator uses it to turn a wrong guess of the verifier's challenge into a right one exactly.
--
--   Differences from the source:
--   - encoding: registers V, K, VK; first qubit of VK; |ψ⟩_V|0⟩_K → V = Qubits a, K = Qubits k, VK = Qubits (a + k) with V on the first a wires; the first qubit is wire 0 (0 < a + k); vectors as functions Qubits a → ℂ with Σ|ψᵢ|² = 1; reason: the paper's setting; the first qubit must exist for the measurement to be defined
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §7.2 p. 50, Lemma 16 (adapted from [Wat09])

import Mathlib
import Definitions.Def_NovyPQZK_Main_Quantum

namespace NovyPQZK.Main

open QAlgorithms
open scoped Matrix

theorem lemma_16 (a k : ℕ) (hak : 0 < a + k) (Q : Matrix (Qubits (a + k)) (Qubits (a + k)) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Qubits (a + k)) ℂ) :
    let proj : Bool → Matrix (Qubits (a + k)) (Qubits (a + k)) ℂ := fun b =>
      diagProj (fun z : Qubits (a + k) => z ⟨0, hak⟩) b
    let inp : (Qubits a → ℂ) → Qubits (a + k) → ℂ := fun ψ z =>
      ψ (fstPart z) * if sndPart z = (fun _ => false) then 1 else 0
    let p : Bool → (Qubits a → ℂ) → ℝ := fun b ψ => ∑ z, ‖((proj b * Q).mulVec (inp ψ)) z‖ ^ 2
    let ψb : Bool → (Qubits a → ℂ) → Qubits (a + k) → ℂ := fun b ψ z =>
      ((proj b * Q).mulVec (inp ψ)) z / ((Real.sqrt (p b ψ) : ℝ) : ℂ)
    let UWat : Matrix (Qubits (a + k)) (Qubits (a + k)) ℂ :=
      Q * ((2 : ℂ) • diagProj (fun z : Qubits (a + k) => decide (sndPart z = fun _ => false)) true - 1) * Qᴴ
    (∀ ψ : Qubits a → ℂ, ∑ i, ‖ψ i‖ ^ 2 = 1 → p false ψ = 1 / 2 ∧ p true ψ = 1 / 2) →
      ∀ ψ : Qubits a → ℂ, ∑ i, ‖ψ i‖ ^ 2 = 1 → ψb true ψ = UWat.mulVec (ψb false ψ) := by sorry

end NovyPQZK.Main
