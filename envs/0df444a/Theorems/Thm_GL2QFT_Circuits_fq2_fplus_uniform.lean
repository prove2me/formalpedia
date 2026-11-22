-- Prove2me | Theorems.Thm_GL2QFT_Circuits_fq2_fplus_uniform
-- name    : GL2QFT.Circuits.fq2_fplus_uniform
-- status  : Open
-- author  : @dmitry
-- created : 2026-11-22T08:18:42.977197+00:00
-- url     : https://prove2.me/theorems/463905ff-f32d-4b2d-af6e-61364a53ec42
-- title:
--   Uniform circuit implementation of the additive Fourier transform on the quadratic extension $\mathbb{F}_{q^2}$
-- statement:
--   Over the polynomial-basis encoding `fq2Code` of $\mathbb{F}_{q^2} \cong \mathbb{F}_p^{2r}$, the additive Fourier transform with trace-paired kernel
--
--   $$|x\rangle \mapsto \frac{1}{q} \sum_{y \in \mathbb{F}_{q^2}} \psi(\operatorname{tr}_{\mathbb{F}_{q^2}/\mathbb{F}_q}(xy)) |y\rangle$$
--
--   factors via an $\mathbb{F}_p$-linear basis change of variables into $2r$ parallel cyclic transforms $\mathrm{QFT}_p^{\otimes 2r}$ and is uniformly implemented in Clifford+$T$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §§6.4.1 & 6.5.3 / App. D.2 (Lemmas 6.8, 6.32, eq. (310), pp. 41, 54, 96)

import Definitions.Def_GL2QFT_Circuits_Leaves

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem fq2_fplus_uniform :
    UniformlyImplementsOn (fun _ => True)
      (fun D => fq2Code D)
      (fun D => fq2Code D)
      (fun D => Matrix.of fun (y x : D.Fq2) =>
        FieldData.isqrt (D.q ^ 2) * D.psi (D.tr (x * y))) := by sorry

end Circuits
end GL2QFT
