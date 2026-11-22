-- Prove2me | Theorems.Thm_GL2QFT_Circuits_dlog2_uniform
-- name    : GL2QFT.Circuits.dlog2_uniform
-- status  : Open
-- author  : @dmitry
-- created : 2026-11-22T08:18:42.163596+00:00
-- url     : https://prove2.me/theorems/73ea1d8a-d491-4505-8e9a-83f8cc55e026
-- title:
--   Uniform circuit implementation of discrete logarithm in the quadratic extension $\mathbb{F}_{q^2}^\times$
-- statement:
--   Over the polynomial-basis encoding `fq2Code` of $z \in \mathbb{F}_{q^2}$, the discrete-logarithm map relative to the primitive element $h \in \mathbb{F}_{q^2}^\times$ sending $|0\rangle \mapsto |0, 0\rangle$ (`none`) and $|h^k\rangle \mapsto |1, k\rangle$ (`some k`, $k \in \mathbb{Z}/(q^2 - 1)\mathbb{Z}$) is uniformly implemented in Clifford+$T$ with `poly(log q, log(1/ε))` gates via Shor's abelian hidden-subgroup discrete-logarithm algorithm over $\mathbb{F}_{q^2}^\times$ and reversible finite-field exponentiation uncomputation.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §§6.4.1 & 6.5.3 (Lemmas 6.8, 6.29, 6.30, 6.32, pp. 41, 53–55, 93–96)

import Definitions.Def_GL2QFT_Circuits_Leaves

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem dlog2_uniform :
    UniformlyImplementsOn (fun _ => True)
      (fun D => fq2Code D)
      (fun D c => match c with
        | none => boolAppCode (fun k : D.Lab2 => packNat 1 D.labW ![k.val]) (false, 0)
        | some k => boolAppCode (fun k : D.Lab2 => packNat 1 D.labW ![k.val]) (true, k))
      (fun D => Matrix.of fun (c : Option D.Lab2) (z : D.Fq2) =>
        match c with
        | none => if z = 0 then 1 else 0
        | some k => if z ≠ 0 ∧ (D.dlog2 z : D.Lab2) = k then 1 else 0) := by sorry

end Circuits
end GL2QFT
