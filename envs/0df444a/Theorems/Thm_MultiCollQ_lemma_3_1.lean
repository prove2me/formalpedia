-- Prove2me | Theorems.Thm_MultiCollQ_lemma_3_1
-- name    : MultiCollQ.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:14:45.791012+00:00
-- url     : https://prove2.me/theorems/c31e3462-f969-4fde-a20f-fcaeae0c77c9
-- title:
--   Lemma 3.1 — local boundary crossing and commutator bounds $\|BQ_x(I-B)\|\le\|[B,Q_x]\|\le2\sqrt{2b/m_H-b^2/m_H^2}\le2\sqrt{2b/m_H}$
-- statement:
--   Fix an input $x$ and a partial injection $H$ with $x\notin\mathrm{dom}(H)$; put $Y_H=[N]\setminus\mathrm{im}(H)$, $m_H=N-|H|$ and $H_y=H[x\mapsto y]$, and let $F_{x,H}=\mathrm{span}\{|H\rangle,|H_y\rangle:y\in Y_H\}$. Let $E\subseteq Y_H$, $b=|E|$ and
--
--   $$
--   B=\sum_{y\in E}|H_y\rangle\langle H_y| .
--   $$
--
--   Then, on $F_{x,H}$ and allowing arbitrary auxiliary registers,
--
--   $$
--   \|BQ_x(I-B)\|\le\|[B,Q_x]\|\le2\sqrt{\frac{2b}{m_H}-\frac{b^2}{m_H^2}}\le2\sqrt{\frac{2b}{m_H}},
--   $$
--
--   where $Q_x$ is the compressed forward query at input $x$ (Definition 2.3).
--
--   This single-query estimate drives every growth bound of §3.
--
--   **Formalization Note** $Q_x$ is `CompPermOracle.cpOAt x`; operators act on $\mathrm{Aux}\otimes W\otimes L$ for an arbitrary finite type $\mathrm{Aux}$.
--
--   Differences from the source:
--   - encoding: the norms on $W\otimes F_{x,H}$ with arbitrary auxiliary registers → operator norms of $I_{\mathrm{Aux}}\otimes I_W\otimes B$ and $I_{\mathrm{Aux}}\otimes Q_x$ on the whole space $\mathrm{Aux}\otimes W\otimes L$; reason: $B$ is supported in $F_{x,H}$ and $Q_x$ preserves $F_{x,H}$ and its orthogonal complement, so all three norms equal those on the subspace
--   - encoding: $Q_x=(I_W\otimes C_x)U_x(I_W\otimes C_x)$ (2.5) → `CompPermOracle.cpOAt x` $=I\otimes C_xQ_{x,\bot}C_x^\dagger+\sum_yS_y\otimes C_xQ_{x,y}C_x^\dagger$; reason: the same operator, since $C_x$ is self-adjoint
--   - encoding: $[N]$ → `Fin N` (0-based); reason: Lean convention; same instances
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; PDF sha256 e20a0870…), Lemma 3.1, p.20 (notation p.19)

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO

namespace MultiCollQ

open CompPermOracle

/-- Lemma 3.1 (Local boundary crossing and commutator bounds) (Peng, Hou, Dong, manuscript
(Oct. 2026), p.20). Fix an input `x` and a partial injection `H` with `x ∉ dom(H)`, let
`Y_H = [N] \ im(H)`, `m_H = N − |H|`, `H_y = H[x ↦ y]`, and let `E ⊆ Y_H`, `b = |E|`,
`B = Σ_{y ∈ E} |H_y⟩⟨H_y|`. With arbitrary auxiliary registers,
`‖B Q_x (I − B)‖ ≤ ‖[B, Q_x]‖ ≤ 2√(2b/m_H − b²/m_H²) ≤ 2√(2b/m_H)` (3.5).

**Formalization Note.** `Q_x` is `CompPermOracle.cpOAt x` on `W ⊗ L` (`W = [N] ∪ {⊥}`), equal to
the paper's `(I_W ⊗ C_x)U_x(I_W ⊗ C_x)` (2.5) since `C_x` is self-adjoint. Arbitrary auxiliary
registers are a finite type `Aux`, and the operators are `I_Aux ⊗ I_W ⊗ B` and `I_Aux ⊗ Q_x` on
the whole space `Aux ⊗ W ⊗ L`. The paper states the norms on `W ⊗ F_{x,H}` (with auxiliary
registers); `B` is supported in `F_{x,H}` and `Q_x` preserves `F_{x,H}` and its orthogonal
complement, so both norms equal those on the subspace. -/
theorem lemma_3_1 {N : ℕ} {Aux : Type} [Fintype Aux] [DecidableEq Aux] (x : Fin N)
    (H : PartialPerm N) (hx : NotInDom H x) (E : Finset (Fin N)) (hE : E ⊆ freeIm H) :
    let m : ℝ := (N : ℝ) - size H
    let bE : ℝ := E.card
    let B0 : Hil (PartialPerm N) →L[ℂ] Hil (PartialPerm N) :=
      ∑ y ∈ E, ketBra (ket (addPair H x y)) (ket (addPair H x y))
    let B : Hil (Aux × (Ans N × PartialPerm N)) →L[ℂ] Hil (Aux × (Ans N × PartialPerm N)) :=
      opTensor (1 : Hil Aux →L[ℂ] Hil Aux) (opTensor (1 : Hil (Ans N) →L[ℂ] Hil (Ans N)) B0)
    let Q : Hil (Aux × (Ans N × PartialPerm N)) →L[ℂ] Hil (Aux × (Ans N × PartialPerm N)) :=
      opTensor (1 : Hil Aux →L[ℂ] Hil Aux) (cpOAt x)
    ‖B ∘L Q ∘L (1 - B)‖ ≤ ‖B ∘L Q - Q ∘L B‖ ∧
      ‖B ∘L Q - Q ∘L B‖ ≤ 2 * Real.sqrt (2 * bE / m - bE ^ 2 / m ^ 2) ∧
      2 * Real.sqrt (2 * bE / m - bE ^ 2 / m ^ 2) ≤ 2 * Real.sqrt (2 * bE / m) := by sorry

end MultiCollQ
