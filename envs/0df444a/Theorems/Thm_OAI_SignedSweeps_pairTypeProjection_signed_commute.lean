-- Prove2me | Theorems.Thm_OAI_SignedSweeps_pairTypeProjection_signed_commute
-- name    : OAI.SignedSweeps.pairTypeProjection_signed_commute
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T00:09:48.035198+00:00
-- url     : https://prove2.me/theorems/4386c064-1334-4a40-b529-65918ff9f063
-- title:
--   Signed type projections commute with the signed permutation action
-- statement:
--   The projection onto a signed type is equivariant for the signed action of the symmetric group.
--
--   Let $C$ be a finite set and $W_p=\ell^2\big((C\sqcup C)^p\big)$, on which $S_p$ acts by the signed action $(\rho(g)f)(w)=\varepsilon(g,w)f(w\circ g)$, where $\varepsilon(g,w)$ is the sign of the permutation induced between the odd positions of $w$. For $u+v=p$, $\alpha\vdash u$, $\beta\vdash v$, the type projection $P_{\alpha,\beta}$ is the sum, over placements of $u$ even sites among the $p$ sites, of the tensor product of the projections onto the $S^\alpha$-isotypic part on the even sites and the $S^\beta$-isotypic part on the odd sites.
--
--   For every $g\in S_p$,
--
--   $$
--   P_{\alpha,\beta}\,\rho(g)=\rho(g)\,P_{\alpha,\beta}.
--   $$
--
--   Thus the range of $P_{\alpha,\beta}$ is a representation of $S_p$, which is the induced module of $S^\alpha\otimes S^{\beta^t}$ tensored with a multiplicity space.
--
--   **Formalization Note** The upstream statement is reproduced verbatim from `SignedPair.lean`.
-- source:
--   OpenAI, "Signed tensor densities and diagram budgets for the Thorp shuffle" (September 26, 2026), openai/math preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf, Section 3, eq. (8) and the surrounding definition of the signed action. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SignedSweeps/SignedPair.lean#L48-L54

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs
import Definitions.Def_OAISignedSweepsProofDefs2

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

theorem pairTypeProjection_signed_commute {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) (g : SymmetricGroup p) :
    pairTypeProjection h α β C * signedWordRepresentation p C g =
      signedWordRepresentation p C g * pairTypeProjection h α β C := by sorry

end SignedSweeps
end
end OAI
