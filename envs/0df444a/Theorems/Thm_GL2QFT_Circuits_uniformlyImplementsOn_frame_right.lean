-- Prove2me | Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_frame_right
-- name    : GL2QFT.Circuits.uniformlyImplementsOn_frame_right
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T04:38:38.29094+00:00
-- url     : https://prove2.me/theorems/4a580842-397b-41df-8fdd-a9f6b314636f
-- title:
--   Right tensor framing $\Phi \otimes I_B$ of an equal-width uniformly implemented family
-- statement:
--   Suppose $\Phi(D) : \mathbb{C}^{X(D)} \to \mathbb{C}^{Y(D)}$ is uniformly implemented on $P$ between codes $c_{\mathrm{in}}, c_{\mathrm{out}}$ of equal register width $w(D)$, and let $c_B(D) : B(D) \to \{0,1\}^{b_W(D)}$ be an injective trailing register code such that both $w(D)$ and $b_W(D)$ are polynomial-time computable from the binary encoding of $D$. Then $\Phi(D) \otimes I_{B(D)}$ is uniformly implemented on $P$ with codes $c_{\mathrm{in}} \Vert c_B$ and $c_{\mathrm{out}} \Vert c_B$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.2 (pp. 43–44, Figure 13), parallel wire action with trailing spectator registers

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem uniformlyImplementsOn_frame_right {P : FieldData → Prop} {X Y B : FieldData → Type} [∀ D, Fintype (X D)] [∀ D, Fintype (Y D)] [∀ D, Fintype (B D)] [∀ D, DecidableEq (B D)] {w bW : FieldData → ℕ} {cin : ∀ D, X D → Qubits (w D)} {cout : ∀ D, Y D → Qubits (w D)} (cb : ∀ D, B D → Qubits (bW D)) {Φ : ∀ D, Matrix (Y D) (X D) ℂ} (h : UniformlyImplementsOn P cin cout Φ) (hcb : ∀ D, P D → Function.Injective (cb D)) (hw : ∃ fw : Str → Str, PolyTimeComputable fw ∧ ∀ D, P D → fw D.encData = encNat (w D)) (hbw : ∃ fb : Str → Str, PolyTimeComputable fb ∧ ∀ D, P D → fb D.encData = encNat (bW D)) : UniformlyImplementsOn P (fun D => appendCode (cin D) (cb D)) (fun D => appendCode (cout D) (cb D)) (fun D => frameMatRight (Φ D)) := by sorry

end Circuits
end GL2QFT
