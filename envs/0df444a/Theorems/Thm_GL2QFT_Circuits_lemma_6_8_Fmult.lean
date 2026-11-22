-- Prove2me | Theorems.Thm_GL2QFT_Circuits_lemma_6_8_Fmult
-- name    : GL2QFT.Circuits.lemma_6_8_Fmult
-- status  : Open
-- author  : @dmitry
-- created : 2026-11-22T06:00:26.079884+00:00
-- url     : https://prove2.me/theorems/ac4a360e-c708-420f-b341-6fbb00b61290
-- title:
--   Uniform circuit implementation of the multiplicative Fourier transform $\mathfrak{F}_\times$
-- statement:
--   Over the multiplicative domain of the tagged register (`|0⟩_+` fixed and `|g^d⟩_×` indexed by $d \in \mathbb{Z}/(q-1)\mathbb{Z}$), the multiplicative Fourier transform $\mathfrak{F}_\times$ reduces to a controlled $\mathrm{QFT}_{q-1}$ on the exponent field conditioned on regime flag $1$, hence is uniformly implemented in Clifford+$T$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.1, Lemma 6.8 eq. (120) (p. 41)

import Definitions.Def_GL2QFT_Circuits_Leaves

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem lemma_6_8_Fmult : UniformlyImplementsOn (fun _ => True) (fun D c => D.tagCode (D.xEmb c)) (fun D c => D.tagCode (D.xEmb c)) (fun D => phiFmult D) := by sorry

end Circuits
end GL2QFT
