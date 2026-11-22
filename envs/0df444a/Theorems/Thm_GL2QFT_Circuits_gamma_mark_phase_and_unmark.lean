-- Prove2me | Theorems.Thm_GL2QFT_Circuits_gamma_mark_phase_and_unmark
-- name    : GL2QFT.Circuits.gamma_mark_phase_and_unmark
-- status  : Open
-- author  : @dmitry
-- created : 2026-11-22T04:38:43.778411+00:00
-- url     : https://prove2.me/theorems/7efbbd8a-de53-4d19-bcc7-6fb9c02c6ff7
-- title:
--   Uniform reversible nontriviality flag computation, $-1$ phase on trivial character, and uncomputation
-- statement:
--   Over the multiplicative domain of the tagged field register (`Option D.Lab` coded by `tagCode ∘ xEmb`), both of the following reversible subcircuits are uniformly implemented:
--
--   1. Detecting whether the character label is trivial ($\alpha = 1$, applying phase $-1$) or nontrivial ($\alpha \in X_q \setminus \{1\}$, writing the auxiliary Boolean flag `isNontrivLab`), mapping `tagCode ∘ xEmb` to `gammaTaggedCode`.
--
--   2. Uncomputing `isNontrivLab` cleanly from `gammaTaggedCode` back to `tagCode ∘ xEmb`.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.1, Theorem 6.10 proof (p. 42, eq. (122)), flag detection and uncomputation

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem gamma_mark_phase_and_unmark : UniformlyImplementsOn (fun _ => True) (fun D c => D.tagCode (D.xEmb c)) (fun D c => gammaTaggedCode D c) (fun D => Matrix.diagonal fun c => match c with | none => 1 | some α => if α = 0 then -1 else 1) ∧ UniformlyImplementsOn (fun _ => True) (fun D c => gammaTaggedCode D c) (fun D c => D.tagCode (D.xEmb c)) (fun _ => 1) := by sorry

end Circuits
end GL2QFT
