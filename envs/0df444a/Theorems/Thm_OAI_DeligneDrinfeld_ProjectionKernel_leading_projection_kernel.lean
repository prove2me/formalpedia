-- Prove2me | Theorems.Thm_OAI_DeligneDrinfeld_ProjectionKernel_leading_projection_kernel
-- name    : OAI.DeligneDrinfeld.ProjectionKernel.leading_projection_kernel
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T18:44:25.917741+00:00
-- url     : https://prove2.me/theorems/da4d493d-4fc2-46cc-b099-ca4fd399bb20
-- title:
--   Proposition 4.4, kernel form (OpenAI, Deligne–Drinfeld) — a mod-2 solution whose leading part dies when A is set to 0 has zero leading part
-- statement:
--   Everything is over $\mathbb F_2$. Let $\mathfrak L(x, y)$ and $\mathfrak L(A, C, B)$ be free Lie algebras over $\mathbb F_2$, with associative envelopes $\iota$, and let $Q$ be the substitution $A \mapsto x^2$, $C \mapsto xy - yx$, $B \mapsto y$ on associative words (`QuadraticLeading.under p = Q(ι p)`). Let $\psi \in \mathfrak L(x, y)$, $p \in \mathfrak L(A, C, B)$ and $n > 2$, $r \in \mathbb N$, and suppose:
--
--   1. $Q(\iota(p)) = \iota(\psi)$;
--   2. $\iota(p)$ is homogeneous of weight $n$, where $A$ and $C$ weigh $2$ and $B$ weighs $1$;
--   3. every word of $\iota(p)$ contains $B$ at least $r$ times;
--   4. $\psi$ satisfies the mod-2 forms of the three defining equations: antisymmetry $\psi + \psi(y, x) = 0$, the special identity $[x, \psi(y, x)] + [-x-y, \psi(y, -x-y)] = 0$, and the pentagon in $\mathfrak t_4$ over $\mathbb F_2$ (`BaseChangeEquations.antisymmetry`, `special`, `pentagon`);
--   5. the retraction $\mathfrak L(A, C, B) \to \mathfrak L(A, C, B)$ that kills $A$ and fixes $C$ and $B$ (`LetterRetraction.lie`) sends $p_{[r]}$ to $0$, where $p_{[r]}$ is the $B$-count-$r$ part of $p$ (`LieGrading.piece bCount r p`).
--
--   Then $p_{[r]} = 0$.
--
--   OpenAI, *The Deligne–Drinfeld conjecture* (September 23, 2026), p. 20: “Proposition 4.4. For $n > 2$ and every $r \ge 0$, the leading projection $\mathrm{gr}^r L_n \longrightarrow \mathrm{Lie}_{\mathbb F_2}\langle C, B\rangle$, $\chi \mapsto \chi(0, C, B)$ is injective.” This statement is OpenAI's Lean theorem `OAI.DeligneDrinfeld.ProjectionKernel.leading_projection_kernel` (`lean/OAI/Algebra/Drinfeld`, Apache-2.0): the injectivity of the leading projection, stated for the reduction mod 2 of a solution as “kernel is zero” on the count-$r$ piece. All objects are OpenAI's, from the bundle `Def_DeligneDrinfeldInternals`. Published as one of the intermediate statements through which the proof of `OAI.DeligneDrinfeld.main` is checked in pieces.
-- source:
--   OpenAI, The Deligne–Drinfeld conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf, p. 20, Proposition 4.4; Lean: https://github.com/openai/math/tree/main/lean/OAI/Algebra/Drinfeld (Apache-2.0)

import Mathlib
import Definitions.Def_DeligneDrinfeldInternals

namespace OAI.DeligneDrinfeld.ProjectionKernel

theorem leading_projection_kernel  {ψ : FreeLieAlgebra OAI.DeligneDrinfeld.ProjectionKernel.K Bool}
    {p : FreeLieAlgebra OAI.DeligneDrinfeld.ProjectionKernel.K OAI.DeligneDrinfeld.RowTwo.Slot} {n r : ℕ} (hn : 2 < n)
    (hp : OAI.DeligneDrinfeld.QuadraticLeading.under p = OAI.DeligneDrinfeld.AssociativeElimination.embed ψ)
    (hw :
      OAI.DeligneDrinfeld.AssociativeElimination.embed p ∈
        OAI.DeligneDrinfeld.WordGrading.homogeneous OAI.DeligneDrinfeld.ExactPentagon.weight n)
    (hfilter :
      OAI.DeligneDrinfeld.AssociativeElimination.embed p ∈
        OAI.DeligneDrinfeld.WordGrading.above OAI.DeligneDrinfeld.RowKernel.bCount r)
    (hanti : OAI.DeligneDrinfeld.BaseChangeEquations.antisymmetry ψ = 0)
    (hspecial : OAI.DeligneDrinfeld.BaseChangeEquations.special ψ = 0)
    (hpent : OAI.DeligneDrinfeld.BaseChangeEquations.pentagon ψ = 0)
    (hzero :
      (OAI.DeligneDrinfeld.LetterRetraction.lie fun a ↦ a ≠ OAI.DeligneDrinfeld.RowTwo.Slot.A)
          (OAI.DeligneDrinfeld.LieGrading.piece OAI.DeligneDrinfeld.RowKernel.bCount r p) =
        0) :
    OAI.DeligneDrinfeld.LieGrading.piece OAI.DeligneDrinfeld.RowKernel.bCount r p = 0 := by
  sorry

end OAI.DeligneDrinfeld.ProjectionKernel
