-- Prove2me | Theorems.Thm_GL2QFT_Circuits_qftModN_uniform
-- name    : GL2QFT.Circuits.qftModN_uniform
-- status  : Open
-- author  : @dmitry
-- created : 2026-11-22T06:00:30.322149+00:00
-- url     : https://prove2.me/theorems/ef37bfd7-4f2e-46b4-b021-cbfb4fdf2f95
-- title:
--   Uniform polynomial-size Clifford+$T$ synthesis of the cyclic quantum Fourier transform $\mathrm{QFT}_N$
-- statement:
--   For any predicate $P(D)$ and integer modulus family $N(D)$ with $1 \le N(D) \le 2^{W(D)}$ where $N(D)$ is polynomial-time computable in self-delimiting binary (`encBin`) and the wire width $W(D) = \mathrm{poly}(\log q)$ is polynomial-time computable in unary (`encNat`), there exists a uniform Clifford+$T$ circuit family implementing the cyclic Fourier transform
--
--   $$(\mathrm{QFT}_N)_{y,x} = \frac{1}{\sqrt{N}} e^{2\pi i x y / N}, \qquad x, y \in \mathbb{Z}/N\mathbb{Z}$$
--
--   to operator-norm error $2^{-k}$ in binary register encoding.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.1 & §2.2 (p. 41, Kitaev / Cleve–Watrous phase estimation for QFT_N)

import Definitions.Def_GL2QFT_Circuits_Leaves

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem qftModN_uniform {P : FieldData → Prop} (N W : FieldData → ℕ) [∀ D, NeZero (N D)] (hN : ∀ D, P D → 1 ≤ N D ∧ N D ≤ 2 ^ W D) (hfN : ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ D, P D → f D.encData = LocalHamiltonian.encBin (N D)) (hfW : ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ D, P D → f D.encData = encNat (W D)) (hWbnd : ∃ c : ℕ, ∀ D, P D → W D ≤ c * (Nat.log 2 D.q + 2) ^ c) : UniformlyImplementsOn P (fun D => zmodCode (W D) (N D)) (fun D => zmodCode (W D) (N D)) (fun D => qftModMat (N D)) := by sorry

end Circuits
end GL2QFT
