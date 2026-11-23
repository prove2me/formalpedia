-- Prove2me | Theorems.Thm_GL2QFT_Circuits_totalA_hard_entry
-- name    : GL2QFT.Circuits.totalA_hard_entry
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:35:56.107332+00:00
-- url     : https://prove2.me/theorems/83fc1004-13c2-4686-8ae5-4579620733d4
-- title:
--   Entrywise identification of the hard block of `totalA` with $A_\gamma$
-- statement:
--   Fix field data with $q>2$. On a valid input whose two Borel labels are $\rho_\gamma$ and $\rho_{\gamma'}$, the hard entry of the total $A$-matrix at output $(\rho_\gamma,\mu,\rho_{\gamma'})$ is the corresponding entry of $A_\gamma$. Validity forces $\gamma'=\gamma$. In the identity column ($\omega=e$) the column index of $A_\gamma$ is $c_\infty$; in the Weyl column ($\omega=w$, necessarily $\kappa=\chi_{\alpha,\beta}$ with $\alpha+\beta=\gamma$) it is $c_\alpha$.
--
--   $$
--   A_{(\rho_\gamma,\mu,\rho_{\gamma'}),(\rho_\gamma,\kappa,\omega,\rho_{\gamma'})}
--   =(A_\gamma)_{\mu,c}.
--   $$
--
--   This is the entrywise form of equations (143)–(145), and isolates the algebraic content needed by the hard-route register conversion from the circuit and encoding arguments.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.4, equations (143)–(145), pp.46–47; entrywise consequence of `A70_eq_AGamma`.

import Definitions.Def_GL2QFT_Circuits_Leaves
import Theorems.Thm_GL2QFT_Circuits_A70_eq_AGamma

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

/-- Entrywise form of the hard block of `totalA`: validity identifies the two character labels,
and the only possible columns are (143). -/
theorem totalA_hard_entry (D : FieldData) (hq : 2 < D.q)
    (γ γ' : D.Lab) (κ : D.BIrr) (ω : Bool)
    (hv : ValidIn D (.inr γ) κ ω (.inr γ')) (μ : D.Irr) :
    totalA D (.inr γ, μ, .inr γ') ⟨(.inr γ, κ, ω, .inr γ'), hv⟩ =
      D.AGamma γ μ (if ω then (match κ with | .inl ab => some ab.1 | .inr _ => none) else none) := by sorry
