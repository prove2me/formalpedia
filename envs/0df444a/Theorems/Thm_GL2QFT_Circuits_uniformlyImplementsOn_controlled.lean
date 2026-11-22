-- Prove2me | Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_controlled
-- name    : GL2QFT.Circuits.uniformlyImplementsOn_controlled
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T04:38:21.469801+00:00
-- url     : https://prove2.me/theorems/c4e00899-114d-4adb-ba0c-d1dee9860858
-- title:
--   Single-qubit controlled lift of a uniform Clifford+T circuit family
-- statement:
--   Let $\Phi(D) : \mathbb{C}^{X(D)} \to \mathbb{C}^{X(D)}$ be uniformly implemented on $P$ with identical input and output codes $c_{\mathrm{in}}$ of width $w(D)$. Then the controlled operator $|0\rangle\langle 0| \otimes I + |1\rangle\langle 1| \otimes \Phi(D)$ on $\mathbb{C}^{\{\mathrm{false}, \mathrm{true}\} \times X(D)}$ is uniformly implemented on $P$ with the $1 + w(D)$-qubit code prepending the control wire.
--
--   **Formalization Note** Each elementary gate $\{H, S, T, X, \mathrm{CNOT}\}$ admits a controlled implementation with clean ancillas: $CX, CCX, CS, CH$ are exact in Clifford+$T$ and $CT$ is synthesized uniformly via Solovay–Kitaev.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.1 (p. 42, Theorem 6.10, eq. (122)), controlled execution bypassing the zero sentinel

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem uniformlyImplementsOn_controlled {P : FieldData → Prop} {X : FieldData → Type} [∀ D, Fintype (X D)] {w : FieldData → ℕ} {cin : ∀ D, X D → Qubits (w D)} {Φ : ∀ D, Matrix (X D) (X D) ℂ} (h : UniformlyImplementsOn P cin cin Φ) : UniformlyImplementsOn P (fun D => boolAppCode (cin D)) (fun D => boolAppCode (cin D)) (fun D => ctrlMat 1 (Φ D)) := by sorry

end Circuits
end GL2QFT
