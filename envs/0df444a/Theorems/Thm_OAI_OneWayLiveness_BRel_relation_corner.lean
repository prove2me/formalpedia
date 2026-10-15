-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_BRel_relation_corner
-- name    : OAI.OneWayLiveness.BRel.relation_corner
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:20:15.746566+00:00
-- url     : https://prove2.me/theorems/9b1e12f1-a169-4c4d-87fc-6243f29787eb
-- title:
--   A partial identity inside an idempotent relation yields a corner isomorphic to a full relation monoid
-- statement:
--   Let $H$ be a set and let $\mathcal B(H)$ be the monoid of binary relations on $H$. Its product is $(RS)(x,z)\iff\exists y:\ R(x,y)\wedge S(y,z)$, and its identity is the equality relation. For $F\subseteq H$ let $\Delta_F=\{(x,x):x\in F\}$. For an idempotent $Q\in\mathcal B(H)$, the corner $Q\,\mathcal B(H)\,Q=\{Z: QZ=Z=ZQ\}$ is a monoid with identity $Q$.
--
--   **Theorem.** Let $P\in\mathcal B(H)$ be idempotent, $P^2=P$, and let $F\subseteq H$ satisfy
--   $$
--   \Delta_F\,P\,\Delta_F=\Delta_F ,
--   $$
--   that is, for $x,y\in F$, $P(x,y)$ holds iff $x=y$. Put $Q=P\,\Delta_F\,P$. Then:
--   1. $Q$ is idempotent, $Q^2=Q$;
--   2. there is a monoid isomorphism $\theta:Q\,\mathcal B(H)\,Q\to\mathcal B(F)$ given by restriction to $F$:
--   $$
--   \theta(Z)(x,y)\iff Z(x,y)\qquad\text{for all } Z\in Q\,\mathcal B(H)\,Q \text{ and } x,y\in F;
--   $$
--   3. $PQ=Q$ and $QP=Q$.
--
--   So a set $F$ on which an idempotent relation $P$ acts as the identity produces an idempotent $Q$ below $P$ (in the sense $PQ=Q=QP$) whose local monoid is the full relation monoid on $F$. In the rank-loss induction this replaces the relation monoid on $H$ by the relation monoid on a smaller set inside the corner of the current idempotent, so that the inductive hypothesis applies.
--
--   **Formalization Note** Relations are `BRel H`, $\Delta_F$ is `BRel.restrictedId F`, and points of $F$ are elements of the subtype `F`. The statement introduces $Q$ by a `let` and asserts the existence of the proof `hQ : Q * Q = Q` together with a `MulEquiv` from `Corner Q hQ` to `BRel F`. No finiteness of $H$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Relations.lean#L63-L98

import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations

open OAI OAI.OneWayLiveness OAI.OneWayLiveness.BRel
variable {H : Type*}

theorem OAI.OneWayLiveness.BRel.relation_corner {P : BRel H} (hP : P * P = P) (F : Set H)
    (hF : restrictedId F * P * restrictedId F = restrictedId F) :
    let Q := P * restrictedId F * P
    ∃ hQ : Q * Q = Q, ∃ θ : Corner Q hQ ≃* BRel F,
      (∀ z x y, (θ z).holds x y ↔ z.val.holds x.val y.val) ∧ P * Q = Q ∧ Q * P = Q := by sorry
