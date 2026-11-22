-- Prove2me | Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_frame
-- name    : GL2QFT.Circuits.uniformlyImplementsOn_frame
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T04:37:54.015392+00:00
-- url     : https://prove2.me/theorems/0b5cb2f7-f3f9-47cb-a561-0fe7033e8a50
-- title:
--   Left tensor framing $I_A \otimes \Phi$ of a uniformly implemented family
-- statement:
--   If $\Phi(D) : \mathbb{C}^{X(D)} \to \mathbb{C}^{Y(D)}$ is uniformly implemented on $P$ from $c_{\mathrm{in}}$ to $c_{\mathrm{out}}$, and $c_A(D) : A(D) \to \{0,1\}^{a_W(D)}$ is an injective spectator register code whose bit width $a_W(D)$ is polynomial-time computable from the binary encoding of $D$, then $I_{A(D)} \otimes \Phi(D)$ is uniformly implemented on $P$ with concatenated codes $c_A \Vert c_{\mathrm{in}}$ and $c_A \Vert c_{\mathrm{out}}$:
--
--   $$\bigl((I_A \otimes \Phi)_{(a', y),(a, x)} = \mathbf{1}_{a'=a}\,\Phi_{y, x}\bigr).$$
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §5 & §6.4.2–6.6 (pp. 28–47), tensor framing over spectator registers

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem uniformlyImplementsOn_frame {P : FieldData → Prop} {A X Y : FieldData → Type} [∀ D, Fintype (A D)] [∀ D, Fintype (X D)] [∀ D, Fintype (Y D)] [∀ D, DecidableEq (A D)] {aW inW outW : FieldData → ℕ} (ca : ∀ D, A D → Qubits (aW D)) {cin : ∀ D, X D → Qubits (inW D)} {cout : ∀ D, Y D → Qubits (outW D)} {Φ : ∀ D, Matrix (Y D) (X D) ℂ} (h : UniformlyImplementsOn P cin cout Φ) (hca : ∀ D, P D → Function.Injective (ca D)) (haw : ∃ fw : Str → Str, PolyTimeComputable fw ∧ ∀ D, P D → fw D.encData = encNat (aW D)) : UniformlyImplementsOn P (fun D => appendCode (ca D) (cin D)) (fun D => appendCode (ca D) (cout D)) (fun D => frameMat (Φ D)) := by sorry

end Circuits
end GL2QFT
