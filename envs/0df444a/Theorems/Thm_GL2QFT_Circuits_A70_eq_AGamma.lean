-- Prove2me | Theorems.Thm_GL2QFT_Circuits_A70_eq_AGamma
-- name    : GL2QFT.Circuits.A70_eq_AGamma
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T04:38:18.633617+00:00
-- url     : https://prove2.me/theorems/2779ab02-b746-467f-811c-c1bc527ee351
-- title:
--   Agreement of `A70` on $(\rho_\gamma, \rho_{\gamma'})$ with the published hard block `AGamma`
-- statement:
--   For any finite-field instance $D$ and any valid input $x = (\rho_\gamma, \kappa, \omega, \rho_{\gamma'}) \in \mathrm{InReg}(D)$ to the total $A$-matrix with both Borel labels two-dimensional, validity forces $\gamma' = \gamma$, $\omega = e \implies \kappa = \rho_\gamma$, and $\omega = w \implies \kappa = \chi_{a,b}$ with $a + b = \gamma$. Moreover, whenever $q > 2$, the matrix entry `A70 D (inr γ) (inr γ) κ ω μ` equals the published `AGamma` entry of equations (144)–(145).
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, Definition 5.3 eq. (70) & §6.4.4 eqs. (143)–(145) (pp. 30, 45–46)

import Definitions.Def_GL2QFT_Circuits_Combinators
import Definitions.Def_GL2QFT_Supplement_TotalA
import Definitions.Def_GL2QFT_AGamma

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem A70_eq_AGamma (D : FieldData) : (∀ x : InReg D, ∀ γ γ' : D.Lab, x.1.1 = .inr γ → x.1.2.2.2 = .inr γ' → γ' = γ ∧ (x.1.2.2.1 = false → x.1.2.1 = .inr γ) ∧ (∀ ab, x.1.2.2.1 = true → x.1.2.1 = .inl ab → ab.1 + ab.2 = γ)) ∧ (2 < D.q → ∀ (γ : D.Lab) (c : Option D.Lab) (μ : D.Irr), let κ : D.BIrr := match c with | none => .inr γ | some α => .inl (α, γ - α); let ω : Bool := c.isSome; A70 D (.inr γ) (.inr γ) κ ω μ = D.AGamma γ μ c) := by sorry

end Circuits
end GL2QFT
