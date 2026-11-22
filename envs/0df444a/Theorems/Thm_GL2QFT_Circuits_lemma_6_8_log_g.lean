-- Prove2me | Theorems.Thm_GL2QFT_Circuits_lemma_6_8_log_g
-- name    : GL2QFT.Circuits.lemma_6_8_log_g
-- status  : Open
-- author  : @dmitry
-- created : 2026-11-22T06:00:50.246844+00:00
-- url     : https://prove2.me/theorems/e125db3c-1785-4837-9cad-f95359957f4c
-- title:
--   Uniform circuit implementation of the discrete-logarithm conversion map $\log_g$
-- statement:
--   The conversion map $\log_g : \mathbb{C}[\mathbb{F}_q] \to \mathbb{C}[\{\infty\} \sqcup \mathbb{Z}/(q-1)\mathbb{Z}]$ sending $|0\rangle_+ \mapsto |0\rangle_+$ and $|a\rangle_+ \mapsto |g^d\rangle_\times$ ($g^d = a$, $a \in \mathbb{F}_q^\times$) is uniformly implemented by coherently executing Shor's discrete-logarithm algorithm over $\mathbb{F}_q^\times$ and reversibly uncomputing $|a\rangle_+$ using finite-field modular exponentiation.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.1, Lemma 6.8 eq. (118) (p. 41)

import Definitions.Def_GL2QFT_Circuits_Leaves

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem lemma_6_8_log_g : UniformlyImplementsOn (fun _ => True) (fun D a => D.tagCode (.inl a)) (fun D c => D.tagCode (D.xEmb c)) (fun D => phiLog D) := by sorry

end Circuits
end GL2QFT
