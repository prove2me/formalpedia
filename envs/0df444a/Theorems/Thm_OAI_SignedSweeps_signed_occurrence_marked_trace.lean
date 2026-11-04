-- Prove2me | Theorems.Thm_OAI_SignedSweeps_signed_occurrence_marked_trace
-- name    : OAI.SignedSweeps.signed_occurrence_marked_trace
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T00:09:11.33368+00:00
-- url     : https://prove2.me/theorems/11fa5831-2301-4a0f-a883-0392d801ef39
-- title:
--   A signed occurrence bounds traces in irreducibles by traces on marked words
-- statement:
--   An occurrence of a signed tensor product in a Specht module bounds its traces by traces on the typed space of marked words.
--
--   Let $C$ be a finite set and $W_p=\ell^2\big((C\sqcup C)^p\big)$, on which $S_p$ acts by the signed action $(\rho(g)f)(w)=\varepsilon(g,w)f(w\circ g)$, where $\varepsilon(g,w)$ is the sign of the permutation induced between the odd positions of $w$. For $u+v=p$, $\alpha\vdash u$, $\beta\vdash v$, the type projection $P_{\alpha,\beta}$ is the sum, over placements of $u$ even sites among the $p$ sites, of the tensor product of the projections onto the $S^\alpha$-isotypic part on the even sites and the $S^\beta$-isotypic part on the odd sites.
--
--   Let $p+l=n$ and let $M_{p,l,n}$ be the orthogonal sum, over injections of $l$ distinct marks into $n$ positions, of word spaces on the $p$ unmarked positions, with the action of $S_n$ moving marks and transporting the words, and let $P$ be the corresponding global projection of type $(a,b)$, for $a\vdash u$, $b\vdash v$, $u+v=p$. Let $c\vdash l$ and $\lambda\vdash n$, and assume that $a$ and $b$ have row counts embedded in $C$ and that $S^a\otimes S^{b^t}\otimes S^c$ occurs in $S^\lambda$ as a signed occurrence. Then for coefficients $f,k:S_n\to\mathbb{C}$ acting positively in the regular representation,
--
--   $$
--   \dim S^c\ \operatorname{Re}\operatorname{Tr}_{S^\lambda}\big(\pi_\lambda(f)\pi_\lambda(k)\big)\le\operatorname{Re}\operatorname{Tr}_{M_{p,l,n}}\big(P\,\pi(f)\,\pi(k)\big).
--   $$
--
--   This passes from an irreducible trace to a trace that splits over mark assignments, which is the entry point of the moment induction.
--
--   **Formalization Note** The statement takes an assignment $z$ and an allocation $S$ as witnesses that the sector is nonempty. It is reproduced verbatim from `MarkedTrace.lean`.
-- source:
--   OpenAI, "Signed tensor densities and diagram budgets for the Thorp shuffle" (September 26, 2026), openai/math preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf, Section 3.2, eq. (15), and Section 4.4, eq. (21). Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SignedSweeps/MarkedTrace.lean#L35-L50

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs
import Definitions.Def_OAISignedSweepsProofDefs2

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

theorem signed_occurrence_marked_trace {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (hn : u+v+l=n)
    (a : Partition u) (b : Partition v) (c : Partition l) (lam : Partition n)
    (colorA : Fin (a.1.colLen 0) ↪ C) (colorB : Fin (b.1.colLen 0) ↪ C)
    (hocc : SignedOccurrence hn a b c lam) (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (f k : SymmetricGroup n → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive)
    (hk : (coefficientAction finiteRegularRepresentation k).IsPositive) :
    (spechtDimension c : ℝ) * (LinearMap.trace ℂ (Specht lam)
      (coefficientAction (spechtRepresentation lam) f * coefficientAction (spechtRepresentation lam) k)).re ≤
        (LinearMap.trace ℂ (MarkedWordSpace p l n C)
          (markedTypeProjection hu h a b C * coefficientAction (markedWordRepresentation h C) f *
            coefficientAction (markedWordRepresentation h C) k)).re := by sorry

end SignedSweeps
end
end OAI
