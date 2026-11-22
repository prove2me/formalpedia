-- Prove2me | Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_unpad_out
-- name    : GL2QFT.Circuits.uniformlyImplementsOn_unpad_out
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T06:00:27.871964+00:00
-- url     : https://prove2.me/theorems/40ba689c-372b-44df-83a6-125c95d4f990
-- title:
--   Output-ancilla unpadding for `UniformlyImplementsOn` when unused tagged branches vanish
-- statement:
--   Suppose a uniform Clifford+$T$ circuit family implements $\Phi_z(D) : \mathbb{C}^{X(D)} \to \mathbb{C}^{Z(D)}$ on $P(D)$, where an embedding $\iota(D) : Y(D) \hookrightarrow Z(D)$ encodes $Y(D)$ by appending a single clean trailing bit $|0\rangle$ to $c_{\mathrm{out}}(D)(y)$:
--
--   $$c_Z(D)(\iota(D)(y)) = c_{\mathrm{out}}(D)(y) \Vert 0.$$
--
--   If $\Phi_z(D)$ vanishes on all rows outside $\operatorname{im}(\iota(D))$ whenever $P(D)$ holds, then restricting to rows $\iota(D)(y)$ yields a uniform implementation of $\Phi_z(D) \circ \iota(D)$ on $P$ with unpadded output code $c_{\mathrm{out}}$ (the trailing qubit returns to $|0\rangle$).
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.5 (pp. 50–55, Theorem 6.34), clean ancilla return on extended irrep space

import Definitions.Def_GL2QFT_Circuits_Leaves

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem uniformlyImplementsOn_unpad_out {P : FieldData → Prop} {X Y Z : FieldData → Type} [∀ D, Fintype (X D)] [∀ D, Fintype (Y D)] [∀ D, Fintype (Z D)] {inW outW : FieldData → ℕ} {cin : ∀ D, X D → Qubits (inW D)} {cout : ∀ D, Y D → Qubits (outW D)} {cz : ∀ D, Z D → Qubits (outW D + 1)} {Φz : ∀ D, Matrix (Z D) (X D) ℂ} (ι : ∀ D, Y D → Z D) (h : UniformlyImplementsOn P cin cz Φz) (hι : ∀ D, P D → Function.Injective (ι D)) (hpad : ∀ D y, cz D (ι D y) = Fin.append (cout D y) (fun (_ : Fin 1) => false)) (hvan : ∀ D, P D → ∀ z x, (∀ y, ι D y ≠ z) → Φz D z x = 0) : UniformlyImplementsOn P cin cout (fun D => Matrix.of fun y x => Φz D (ι D y) x) := by sorry

end Circuits
end GL2QFT
