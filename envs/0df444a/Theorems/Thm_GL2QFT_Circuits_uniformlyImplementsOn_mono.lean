-- Prove2me | Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_mono
-- name    : GL2QFT.Circuits.uniformlyImplementsOn_mono
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T04:38:47.815024+00:00
-- url     : https://prove2.me/theorems/fb8ae3d4-074c-427c-80d2-a76c8b1240d9
-- title:
--   Predicate monotonicity of `UniformlyImplementsOn`
-- statement:
--   If a Clifford+$T$ circuit family uniformly implements $\Phi$ on field instances satisfying $P(D)$, and $P'(D) \implies P(D)$ for every $D$, then the same circuit family uniformly implements $\Phi$ on $P'$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §2.2 & §6.5, Remark 6.15 (pp. 12, 48), restricting uniformity predicates

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem uniformlyImplementsOn_mono {P P' : FieldData → Prop} {X Y : FieldData → Type} [∀ D, Fintype (X D)] [∀ D, Fintype (Y D)] {inW outW : FieldData → ℕ} {cin : ∀ D, X D → Qubits (inW D)} {cout : ∀ D, Y D → Qubits (outW D)} {Φ : ∀ D, Matrix (Y D) (X D) ℂ} (h : UniformlyImplementsOn P cin cout Φ) (himp : ∀ D, P' D → P D) : UniformlyImplementsOn P' cin cout Φ := by sorry

end Circuits
end GL2QFT
