-- Prove2me | Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_by_q2
-- name    : GL2QFT.Circuits.uniformlyImplementsOn_by_q2
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T04:37:51.388896+00:00
-- url     : https://prove2.me/theorems/0387f9ad-a23c-4535-ba14-d700864f75a5
-- title:
--   Classical case split of `UniformlyImplementsOn` at $q = 2$ vs. $q > 2$
-- statement:
--   If an operator family $\Phi(D)$ admits a uniform Clifford+$T$ implementation when $P(D) \land (q = 2)$ and another uniform implementation when $P(D) \land (q > 2)$, then $\Phi$ is uniformly implemented on all instances satisfying $P(D)$.
--
--   **Formalization Note** The condition $q = 2$ is equivalent to $p = 2 \land r = 1$, which is decided in polynomial time from the self-delimiting binary encoding of $D$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.5, Remark 6.15 (p. 48) & Theorem 6.14 (p. 47), splitting $q = 2$ from $q > 2$

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem uniformlyImplementsOn_by_q2 {P : FieldData → Prop} {X Y : FieldData → Type} [∀ D, Fintype (X D)] [∀ D, Fintype (Y D)] {inW outW : FieldData → ℕ} {cin : ∀ D, X D → Qubits (inW D)} {cout : ∀ D, Y D → Qubits (outW D)} {Φ : ∀ D, Matrix (Y D) (X D) ℂ} (h2 : UniformlyImplementsOn (fun D => P D ∧ D.q = 2) cin cout Φ) (hgt2 : UniformlyImplementsOn (fun D => P D ∧ 2 < D.q) cin cout Φ) : UniformlyImplementsOn P cin cout Φ := by sorry

end Circuits
end GL2QFT
