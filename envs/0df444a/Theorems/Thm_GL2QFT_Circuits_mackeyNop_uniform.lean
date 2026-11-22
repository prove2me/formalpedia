-- Prove2me | Theorems.Thm_GL2QFT_Circuits_mackeyNop_uniform
-- name    : GL2QFT.Circuits.mackeyNop_uniform
-- status  : Open
-- author  : @dmitry
-- created : 2026-11-22T06:00:33.808815+00:00
-- url     : https://prove2.me/theorems/bff87b90-39ed-455c-87c3-02831f5aac18
-- title:
--   Stage 3 of $F_{\mathrm{GL}_2(\mathbb{F}_q)}$: uniform circuit implementation of Mackey $N_{\mathrm{op}}$
-- statement:
--   On the output of $I \otimes F_B$, the Mackey induction operator `mackeyNopMat` maps `|e, λ, Q, P⟩ ↦ |e, λ, λ, λ, Q, P⟩` on cell $e$, while on cell $w$ ($|x\rangle |\lambda, Q, P\rangle$) it applies the permutation untwister $U^w_{\mathrm{twist}}$ taking `(λ, Q)` to the $T$-character `κ = χ_{a,b}` followed by the additive induction transform $U_{\mathrm{Ind}}^{T < B}$ ($\mathfrak{F}_+$ on $|x\rangle$, phase/shift, and branch merge into $|\tilde{\lambda}, P'\rangle$), yielding a uniform Clifford+$T$ circuit.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.3, Theorem 5.4 & eq. (126) (pp. 30, 44–45)

import Definitions.Def_GL2QFT_Circuits_Leaves

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem mackeyNop_uniform : UniformlyImplementsOn (fun _ => True) (fun D => appendCode (cosetCode D) D.bOutCode) (fun D => mackeyMidCode D) (fun D => mackeyNopMat D) := by sorry

end Circuits
end GL2QFT
