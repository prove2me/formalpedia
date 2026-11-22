-- Prove2me | Theorems.Thm_GL2QFT_Circuits_A70_small_blocks
-- name    : GL2QFT.Circuits.A70_small_blocks
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T04:38:12.091003+00:00
-- url     : https://prove2.me/theorems/1750d52c-b37d-4ee1-96af-bfee8304223b
-- title:
--   Closed-form entries of `A70` for 1D/2D blocks and the $q = 2$ block
-- statement:
--   The small-dimensional blocks of `A70` satisfy the explicit formulas of equations (128)–(139) whenever either Borel label $l$ or $\tilde{l}$ is one-dimensional ($\chi_{\alpha,\beta}$), and for $q = 2$ ($l = \tilde{l} = \rho_0$) the $2\times 2$ block satisfies the exact rotation of equation (147) on the target basis $(|\pi_\theta\rangle, |\mathrm{St}_0\rangle)$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.4, eqs. (128)–(139) & §6.5 Remark 6.15 eq. (147) (pp. 45, 48)

import Definitions.Def_GL2QFT_Circuits_Combinators
import Definitions.Def_GL2QFT_Supplement_TotalA

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem A70_small_blocks (D : FieldData) : (∀ (α β : D.Lab) (hlt : α.val < β.val), A70 D (.inl (α, β)) (.inl (α, β)) (.inl (α, β)) false (.inr (.inr (.inl ⟨(α, β), hlt⟩))) = 1 ∧ A70 D (.inl (α, β)) (.inl (β, α)) (.inl (β, α)) true (.inr (.inr (.inl ⟨(α, β), hlt⟩))) = 1) ∧ (∀ (α : D.Lab), A70 D (.inl (α, α)) (.inl (α, α)) (.inl (α, α)) false (.inr (.inl α)) = (Real.sqrt (D.q / ((D.q : ℝ) + 1)) : ℂ) ∧ A70 D (.inl (α, α)) (.inl (α, α)) (.inl (α, α)) false (.inl α) = (Real.sqrt (1 / ((D.q : ℝ) + 1)) : ℂ) ∧ A70 D (.inl (α, α)) (.inl (α, α)) (.inl (α, α)) true (.inr (.inl α)) = -(D.chi α (-1)) * (Real.sqrt (1 / ((D.q : ℝ) + 1)) : ℂ) ∧ A70 D (.inl (α, α)) (.inl (α, α)) (.inl (α, α)) true (.inl α) = D.chi α (-1) * (Real.sqrt (D.q / ((D.q : ℝ) + 1)) : ℂ)) ∧ (D.q = 2 → A70 D (.inr 0) (.inr 0) (.inr 0) false (.inr (.inl 0)) = (Real.sqrt (2 / 3 : ℝ) : ℂ) ∧ A70 D (.inr 0) (.inr 0) (.inl (0, 0)) true (.inr (.inl 0)) = (Real.sqrt (1 / 3 : ℝ) : ℂ) ∧ ∀ k : {k : D.Lab2 // D.IsCuspLabel k}, A70 D (.inr 0) (.inr 0) (.inr 0) false (.inr (.inr (.inr k))) = (Real.sqrt (1 / 3 : ℝ) : ℂ) ∧ A70 D (.inr 0) (.inr 0) (.inl (0, 0)) true (.inr (.inr (.inr k))) = -(Real.sqrt (2 / 3 : ℝ) : ℂ)) := by sorry

end Circuits
end GL2QFT
