-- Prove2me | Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_adjoint
-- name    : GL2QFT.Circuits.uniformlyImplementsOn_adjoint
-- status  : Open
-- author  : @dmitry
-- created : 2026-11-22T04:38:34.837711+00:00
-- url     : https://prove2.me/theorems/408fe7d0-3431-415d-80f9-887ece03ea4b
-- title:
--   Adjoint inversion of `UniformlyImplementsOn` for unitary operator families
-- statement:
--   If $\Phi(D) : \mathbb{C}^{X(D)} \to \mathbb{C}^{Y(D)}$ is unitary whenever $P(D)$ holds ($\Phi(D)^\dagger \Phi(D) = I$ and $\Phi(D)\Phi(D)^\dagger = I$) and is uniformly implemented on $P$ from $c_{\mathrm{in}}$ to $c_{\mathrm{out}}$, then the adjoint family $D \mapsto \Phi(D)^\dagger$ is uniformly implemented on $P$ from $c_{\mathrm{out}}$ to $c_{\mathrm{in}}$.
--
--   **Formalization Note** Every gate in $\{H, S, T, X, \mathrm{CNOT}\}$ has an exact adjoint over the same set ($S^\dagger = S^3$, $T^\dagger = T^7$), so reversing the circuit via `circInv` blows up size by at most a factor of $7$ and preserves the operator-norm error bound for unitary targets.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.1 & §6.5 (pp. 41–42, 48–50), inversion of Clifford+T circuits

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem uniformlyImplementsOn_adjoint {P : FieldData → Prop} {X Y : FieldData → Type} [∀ D, Fintype (X D)] [∀ D, Fintype (Y D)] {inW outW : FieldData → ℕ} {cin : ∀ D, X D → Qubits (inW D)} {cout : ∀ D, Y D → Qubits (outW D)} {Φ : ∀ D, Matrix (Y D) (X D) ℂ} (h : UniformlyImplementsOn P cin cout Φ) (hu : ∀ D, P D → (Φ D).conjTranspose * (Φ D) = 1 ∧ (Φ D) * (Φ D).conjTranspose = 1) : UniformlyImplementsOn P cout cin (fun D => (Φ D).conjTranspose) := by sorry

end Circuits
end GL2QFT
