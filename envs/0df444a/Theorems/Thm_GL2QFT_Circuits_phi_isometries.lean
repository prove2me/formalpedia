-- Prove2me | Theorems.Thm_GL2QFT_Circuits_phi_isometries
-- name    : GL2QFT.Circuits.phi_isometries
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T04:38:53.652963+00:00
-- url     : https://prove2.me/theorems/dab0fcf7-1411-4009-9ece-cde5dba787e8
-- title:
--   Unitarity of the finite-field Fourier and conversion matrices $\mathfrak{F}_+, \mathfrak{F}_\times, \exp_g, \log_g$
-- statement:
--   For every finite-field instance $D$, the four linear maps of Lemma 6.8 — the additive Fourier transform `phiFplus`, the extended multiplicative Fourier transform `phiFmult`, the exponentiation map `phiExp`, and the discrete-logarithm map `phiLog` — are unitary matrices, and in particular preserve Euclidean norms:
--
--   $$\Phi^\dagger \Phi = I, \qquad \Phi \Phi^\dagger = I, \qquad \|\Phi \psi\|_2 \le \|\psi\|_2.$$
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.1 (p. 41, Lemma 6.8, eqs. (117)–(120)), unitarity of finite-field transforms

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem phi_isometries (D : FieldData) : ((phiFplus D).conjTranspose * phiFplus D = 1 ∧ phiFplus D * (phiFplus D).conjTranspose = 1) ∧ ((phiFmult D).conjTranspose * phiFmult D = 1 ∧ phiFmult D * (phiFmult D).conjTranspose = 1) ∧ ((phiExp D).conjTranspose * phiExp D = 1 ∧ phiExp D * (phiExp D).conjTranspose = 1) ∧ ((phiLog D).conjTranspose * phiLog D = 1 ∧ phiLog D * (phiLog D).conjTranspose = 1) := by sorry

end Circuits
end GL2QFT
