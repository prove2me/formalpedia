-- Prove2me | Theorems.Thm_HarlowTASI_trace_mul_blockScalarOp
-- name    : HarlowTASI.trace_mul_blockScalarOp
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-26T20:49:42.382507+00:00
-- url     : https://prove2.me/theorems/81628844-5488-4ad0-98df-8a1c8c3fd403
-- title:
--   Expectation value of a central operator
-- statement:
--   Let $U:\mathbb C^C\to\bigoplus_\alpha\mathcal H_{r_\alpha}\otimes\mathcal H_{\overline r_\alpha}$ be a linear map ($\dim\mathcal H_{r_\alpha}=d_\alpha$, $\dim\mathcal H_{\overline r_\alpha}=\overline d_\alpha$). For a matrix $\rho$ on $\mathbb C^C$ let $\rho_{\alpha\alpha}$ be the diagonal block $\alpha$ of $U\rho U^\dagger$, $p_\alpha=\mathrm{Re}\,\mathrm{Tr}\,\rho_{\alpha\alpha}$, and $\rho_{r_\alpha}=p_\alpha^{-1}\mathrm{Tr}_{\overline r_\alpha}\rho_{\alpha\alpha}$, $\rho_{\overline r_\alpha}=p_\alpha^{-1}\mathrm{Tr}_{r_\alpha}\rho_{\alpha\alpha}$ (both $0$ when $p_\alpha=0$), as in (5.15). For every $\rho$ and every central operator $L=U^\dagger\big(\bigoplus_\alpha c_\alpha I_\alpha\big)U$,
--   $$\mathrm{Tr}(\rho L)=\sum_\alpha c_\alpha\,\mathrm{Tr}\,\rho_{\alpha\alpha}.$$
--   For a state this is $\mathrm{Tr}(\rho L)=\sum_\alpha p_\alpha c_\alpha$, the form in which the area operator enters the RT formula (5.20).
-- source:
--   Daniel Harlow, TASI Lectures on the Emergence of Bulk Physics in AdS/CFT, arXiv:1802.01040, §5.3 (proof of Theorem 5.2, (1) ⇒ (2)); D. Harlow, Commun. Math. Phys. 354 (2017) 865, arXiv:1607.03901, §5.

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

open Matrix
open scoped Kronecker ComplexOrder

namespace HarlowTASI
theorem trace_mul_blockScalarOp {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    (ρ : Matrix C C ℂ) (c : Fin N → ℂ) :
    (ρ * (Uᴴ * blockScalarOp (dr := dr) (drb := drb) c * U)).trace =
      ∑ a, c a * (diagBlock U ρ a).trace := by sorry
end HarlowTASI
