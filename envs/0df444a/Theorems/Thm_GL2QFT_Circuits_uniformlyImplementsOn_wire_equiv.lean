-- Prove2me | Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_wire_equiv
-- name    : GL2QFT.Circuits.uniformlyImplementsOn_wire_equiv
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:03:41.575802+00:00
-- url     : https://prove2.me/theorems/2a553ed4-8505-495d-8ec8-b29ae3fdbe57
-- title:
--   Uniform implementation under a computable permutation of circuit wires
-- statement:
--   Let a uniform family of circuits implement matrices $\Phi(D)$ on a register of $w(D)$ wires, and let $e_D$ permute those wires. Permuting every gate wire by $e_D$ and precomposing the input and output codes with $e_D$ implements the same matrix $\Phi(D)$, with no increase in circuit size or error.
--
--   Formally, the new input and output codes are $x\mapsto c_{\mathrm{in}}(x)\circ e_D$ and $y\mapsto c_{\mathrm{out}}(y)\circ e_D$. For uniformity of the printed circuit, the statement assumes a polynomial-time transformer $f$ that, on every wire-count encoding and encoded instruction list, applies $e_D$ to every gate wire; this transformer can be computed from the binary code of $D$.
--
--   This is the wire-relabelling counterpart of clean ancillas and tensor framing in §2.2 of the paper. It is useful when a standard branch or frame combinator places control and payload fields in a different order from the tagged register of §6.4.1.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §2.2 (p.12) and §6.4.1 (p.41)

import Definitions.Def_GL2QFT_Circuits_Leaves

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

theorem GL2QFT.Circuits.uniformlyImplementsOn_wire_equiv {P : FieldData → Prop} {X Y : FieldData → Type} [∀ D, Fintype (X D)] [∀ D, Fintype (Y D)] {w : FieldData → ℕ} {cin : ∀ D, X D → Qubits (w D)} {cout : ∀ D, Y D → Qubits (w D)} {Φ : ∀ D, Matrix (Y D) (X D) ℂ} (e : ∀ D, Fin (w D) ≃ Fin (w D)) (h : UniformlyImplementsOn P cin cout Φ) (hf : ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ D, P D → ∀ c : List (Instr (w D)), f (D.encData ++ encNat (w D) ++ encLayer c) = encNat (w D) ++ encLayer (mapCirc (e D).toEmbedding c)) : UniformlyImplementsOn P (fun D x i => cin D x (e D i)) (fun D y i => cout D y (e D i)) Φ := by sorry
