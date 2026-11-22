-- Prove2me | Theorems.Thm_GL2QFT_Circuits_gamma_circuit_identity
-- name    : GL2QFT.Circuits.gamma_circuit_identity
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T04:38:00.807822+00:00
-- url     : https://prove2.me/theorems/b42cecf5-e43e-40a4-bd07-5c72b1d18a57
-- title:
--   Algebraic correctness of the Gauss-phase circuit identity
-- statement:
--   For any finite field $\mathbb{F}_q$ represented by $D$ and any nontrivial multiplicative character $\alpha \in X_q \setminus \{1\}$ (nonzero exponent label $\alpha \neq 0$), applying $\mathfrak{F}_\times$, $\exp_g$, $\mathfrak{F}_+$, $\log_g$, and $\mathfrak{F}_\times$ in sequence to $|\alpha\rangle_\times$ yields
--
--   $$\mathfrak{F}_\times \log_g \mathfrak{F}_+ \exp_g \mathfrak{F}_\times |\alpha\rangle_\times = \frac{g_q(\alpha)}{\sqrt{q}} |\alpha\rangle_\times.$$
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.1, Theorem 6.10 proof & Figure 12 (pp. 42–43), eq. (122)

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem gamma_circuit_identity (D : FieldData) (α : D.Lab) (hα : α ≠ 0) (c : Option D.Lab) : (phiFmult D * phiLog D * phiFplus D * phiExp D * phiFmult D) c (some α) = if c = some α then D.gauss α * FieldData.isqrt D.q else 0 := by sorry

end Circuits
end GL2QFT
