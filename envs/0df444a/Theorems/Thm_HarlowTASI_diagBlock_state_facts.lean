-- Prove2me | Theorems.Thm_HarlowTASI_diagBlock_state_facts
-- name    : HarlowTASI.diagBlock_state_facts
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-26T20:49:57.22999+00:00
-- url     : https://prove2.me/theorems/7b84ddd5-779c-4a8c-97f4-1e0fc71ffd9e
-- title:
--   Block decomposition of a state and its entropies
-- statement:
--   Throughout, $S(X)=-\sum_\lambda\lambda\log\lambda$ is the von Neumann entropy of a Hermitian matrix $X$, the sum running over its eigenvalues with multiplicity ($0\log 0=0$); on non-Hermitian input it is set to $0$. Let $U:\mathbb C^C\to\bigoplus_\alpha\mathcal H_{r_\alpha}\otimes\mathcal H_{\overline r_\alpha}$ be a linear map ($\dim\mathcal H_{r_\alpha}=d_\alpha$, $\dim\mathcal H_{\overline r_\alpha}=\overline d_\alpha$). For a matrix $\rho$ on $\mathbb C^C$ let $\rho_{\alpha\alpha}$ be the diagonal block $\alpha$ of $U\rho U^\dagger$, $p_\alpha=\mathrm{Re}\,\mathrm{Tr}\,\rho_{\alpha\alpha}$, and $\rho_{r_\alpha}=p_\alpha^{-1}\mathrm{Tr}_{\overline r_\alpha}\rho_{\alpha\alpha}$, $\rho_{\overline r_\alpha}=p_\alpha^{-1}\mathrm{Tr}_{r_\alpha}\rho_{\alpha\alpha}$ (both $0$ when $p_\alpha=0$), as in (5.15). If $\rho\succeq0$, then for every block $\alpha$: $\mathrm{Tr}\,\rho_{\alpha\alpha}=p_\alpha$ (it is real), $\mathrm{Tr}_{\overline r_\alpha}\rho_{\alpha\alpha}$ and $\mathrm{Tr}_{r_\alpha}\rho_{\alpha\alpha}$ are Hermitian, and
--   $$S(\mathrm{Tr}_{\overline r_\alpha}\rho_{\alpha\alpha})=-p_\alpha\log p_\alpha+p_\alpha S(\rho_{r_\alpha}),\qquad S(\mathrm{Tr}_{r_\alpha}\rho_{\alpha\alpha})=-p_\alpha\log p_\alpha+p_\alpha S(\rho_{\overline r_\alpha}).$$
--   These are the per-block identities behind the algebraic entropy (5.16).
-- source:
--   Daniel Harlow, TASI Lectures on the Emergence of Bulk Physics in AdS/CFT, arXiv:1802.01040, §5.3 (proof of Theorem 5.2, (1) ⇒ (2)); D. Harlow, Commun. Math. Phys. 354 (2017) 865, arXiv:1607.03901, §5.

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

open Matrix
open scoped Kronecker ComplexOrder

namespace HarlowTASI
theorem diagBlock_state_facts {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    (ρ : Matrix C C ℂ) (hρ : ρ.PosSemidef) (a : Fin N) :
    (diagBlock U ρ a).trace = (blockWeight U ρ a : ℂ) ∧
    (traceRight (diagBlock U ρ a)).IsHermitian ∧
    (traceLeft (diagBlock U ρ a)).IsHermitian ∧
    vonNeumannEntropy (traceRight (diagBlock U ρ a)) =
      Real.negMulLog (blockWeight U ρ a) +
        blockWeight U ρ a * vonNeumannEntropy (blockStateLeft U ρ a) ∧
    vonNeumannEntropy (traceLeft (diagBlock U ρ a)) =
      Real.negMulLog (blockWeight U ρ a) +
        blockWeight U ρ a * vonNeumannEntropy (blockStateRight U ρ a) := by sorry
end HarlowTASI
