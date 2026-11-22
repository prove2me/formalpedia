-- Prove2me | Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_sum
-- name    : GL2QFT.Circuits.uniformlyImplementsOn_sum
-- status  : Open
-- author  : @dmitry
-- created : 2026-11-22T04:38:01.151801+00:00
-- url     : https://prove2.me/theorems/bb31791b-088f-459f-a46c-833975900d9c
-- title:
--   Tagged direct-sum multiplexer for `UniformlyImplementsOn` on distinct register types
-- statement:
--   If $\Phi_0(D) : \mathbb{C}^{X_0(D)} \to \mathbb{C}^{Y_0(D)}$ and $\Phi_1(D) : \mathbb{C}^{X_1(D)} \to \mathbb{C}^{Y_1(D)}$ are both uniformly implemented on $P$, then their block-diagonal direct sum $\Phi_0(D) \oplus \Phi_1(D)$ on $X_0(D) \sqcup X_1(D) \to Y_0(D) \sqcup Y_1(D)$ is uniformly implemented on $P$ with the tag-prefixed direct-sum register codes `sumCode`.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.4 (p. 47, Theorem 6.14), direct sum of block subcircuits over heterogeneous types

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem uniformlyImplementsOn_sum {P : FieldData → Prop} {X₀ X₁ Y₀ Y₁ : FieldData → Type} [∀ D, Fintype (X₀ D)] [∀ D, Fintype (X₁ D)] [∀ D, Fintype (Y₀ D)] [∀ D, Fintype (Y₁ D)] {m₀ m₁ n₀ n₁ : FieldData → ℕ} {cx₀ : ∀ D, X₀ D → Qubits (m₀ D)} {cx₁ : ∀ D, X₁ D → Qubits (m₁ D)} {cy₀ : ∀ D, Y₀ D → Qubits (n₀ D)} {cy₁ : ∀ D, Y₁ D → Qubits (n₁ D)} {Φ₀ : ∀ D, Matrix (Y₀ D) (X₀ D) ℂ} {Φ₁ : ∀ D, Matrix (Y₁ D) (X₁ D) ℂ} (h0 : UniformlyImplementsOn P cx₀ cy₀ Φ₀) (h1 : UniformlyImplementsOn P cx₁ cy₁ Φ₁) : UniformlyImplementsOn P (fun D => sumCode (cx₀ D) (cx₁ D)) (fun D => sumCode (cy₀ D) (cy₁ D)) (fun D => sumMat (Φ₀ D) (Φ₁ D)) := by sorry

end Circuits
end GL2QFT
