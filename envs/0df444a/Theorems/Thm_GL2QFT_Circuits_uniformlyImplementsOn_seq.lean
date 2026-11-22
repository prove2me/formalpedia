-- Prove2me | Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_seq
-- name    : GL2QFT.Circuits.uniformlyImplementsOn_seq
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T04:38:03.348037+00:00
-- url     : https://prove2.me/theorems/db0ebbb9-7c03-4b41-ba3f-c6cee06204cf
-- title:
--   Sequential composition of `UniformlyImplementsOn` families
-- statement:
--   Let $\Phi_1(D) : \mathbb{C}^{X(D)} \to \mathbb{C}^{M(D)}$ and $\Phi_2(D) : \mathbb{C}^{M(D)} \to \mathbb{C}^{Y(D)}$ be uniformly implemented by Clifford+$T$ circuit families on $P$ matching at an intermediate code $c_{\mathrm{mid}}$ of width $w_{\mathrm{mid}}(D)$. Suppose $\Phi_1(D)$ is contractive whenever $P(D)$ holds:
--
--   $$\|\Phi_1(D)\psi\|_2 \le \|\psi\|_2 \quad \forall \psi \in \mathbb{C}^{X(D)}.$$
--
--   Then the composed linear map $D \mapsto \Phi_2(D)\Phi_1(D)$ is uniformly implemented on $P$ from $c_{\mathrm{in}}$ to $c_{\mathrm{out}}$.
--
--   **Formalization Note** Running precision $k+2$ on both subcircuits limits the propagated error to $2^{-(k+2)} + 2^{-(k+2)} = 2^{-(k+1)} \le 2^{-k}$, with total wire count $\max(w_1, w_2)$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4 (pp. 41–47) & §2.2, subadditivity of operator-norm errors under sequential composition

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem uniformlyImplementsOn_seq {P : FieldData → Prop} {X M Y : FieldData → Type} [∀ D, Fintype (X D)] [∀ D, Fintype (M D)] [∀ D, Fintype (Y D)] {inW midW outW : FieldData → ℕ} {cin : ∀ D, X D → Qubits (inW D)} {cmid : ∀ D, M D → Qubits (midW D)} {cout : ∀ D, Y D → Qubits (outW D)} {Φ1 : ∀ D, Matrix (M D) (X D) ℂ} {Φ2 : ∀ D, Matrix (Y D) (M D) ℂ} (h1 : UniformlyImplementsOn P cin cmid Φ1) (h2 : UniformlyImplementsOn P cmid cout Φ2) (hbnd : ∀ D, P D → ∀ ψ : EuclideanSpace ℂ (X D), ‖WithLp.toLp 2 ((Φ1 D).mulVec (WithLp.ofLp ψ))‖ ≤ ‖ψ‖) : UniformlyImplementsOn P cin cout (fun D => Φ2 D * Φ1 D) := by sorry

end Circuits
end GL2QFT
