-- Prove2me | Theorems.Thm_GL2QFT_Circuits_lemma_6_8_Fplus
-- name    : GL2QFT.Circuits.lemma_6_8_Fplus
-- status  : Open
-- author  : @dmitry
-- created : 2026-11-22T06:00:36.654802+00:00
-- url     : https://prove2.me/theorems/ce6eec6f-78ab-40a6-9dcf-52ac1f34c644
-- title:
--   Uniform circuit implementation of the additive finite-field Fourier transform $\mathfrak{F}_+$
-- statement:
--   Over the polynomial-basis additive register $|x\rangle_+$, $x \in \mathbb{F}_q$ ($q = p^r$), the additive Fourier transform
--
--   $$\mathfrak{F}_+ |x\rangle_+ = \frac{1}{\sqrt{q}} \sum_{y \in \mathbb{F}_q} \psi(x y) |y\rangle_+$$
--
--   factors into $r$ parallel cyclic Fourier transforms $\mathrm{QFT}_p^{\otimes r}$ up to an $\mathbb{F}_p$-linear trace change of coordinates and is uniformly implemented in Clifford+$T$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.1, Lemma 6.8 eq. (119) (p. 41)

import Definitions.Def_GL2QFT_Circuits_Leaves

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem lemma_6_8_Fplus : UniformlyImplementsOn (fun _ => True) (fun D a => D.tagCode (.inl a)) (fun D a => D.tagCode (.inl a)) (fun D => phiFplus D) := by sorry

end Circuits
end GL2QFT
