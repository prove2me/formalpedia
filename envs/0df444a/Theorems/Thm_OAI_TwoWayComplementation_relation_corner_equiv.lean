-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_relation_corner_equiv
-- name    : OAI.TwoWayComplementation.relation_corner_equiv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:44:51.869422+00:00
-- url     : https://prove2.me/theorems/3ceb59fd-9b48-4c86-b1cc-3de2f9cfad1e
-- title:
--   Restriction to a subset identifies a corner of the relation monoid with the full relation monoid of the subset
-- statement:
--   For a set $H$ let $\mathcal B(H)$ be the monoid of binary relations on $H$, with product $RS=\{(x,z):\ (x,y)\in R\text{ and }(y,z)\in S\text{ for some }y\in H\}$ (composition in path order) and identity the equality relation $\mathrm{id}_H=\{(x,x):x\in H\}$. For $F\subseteq H$ let $\Delta_F=\{(x,x):x\in F\}$ be the partial identity on $F$. For an idempotent $Q\in\mathcal B(H)$, the corner $Q\,\mathcal B(H)\,Q=\{Z\in\mathcal B(H):\ QZ=Z=ZQ\}$ is a monoid under composition, with identity element $Q$.
--
--   **Theorem.** Let $P\in\mathcal B(H)$ be idempotent, $P^2=P$, and let $F\subseteq H$ satisfy
--   $$
--   \Delta_F\,P\,\Delta_F=\Delta_F ,
--   $$
--   that is, for $x,y\in F$ one has $(x,y)\in P$ if and only if $x=y$. Put $Q=P\,\Delta_F\,P$. Then $Q$ is idempotent, and restriction to $F\times F$ is a monoid isomorphism
--   $$
--   \rho:\ Q\,\mathcal B(H)\,Q\ \longrightarrow\ \mathcal B(F),\qquad \rho(Z)=\{(x,y)\in F\times F:\ (x,y)\in Z\}.
--   $$
--
--   So a subset on which an idempotent relation acts as the identity produces a local monoid $Q\,\mathcal B(H)\,Q$ that is a copy of the full relation monoid of the subset. In the amplification argument for the complementation lower bound, this is how an instance of the problem on the label set $H$ is turned into an instance on a smaller label set $F$.
--
--   **Formalization Note** $\mathcal B(H)$ is `RelationMonoid H`, the opposite of the endomorphism monoid of $H$ in the category of relations, so that its product is composition in path order; `ofRel` and `toRel` convert between its elements and `SetRel H H`. The corner is `hQ.Corner` with the monoid structure `cornerMonoid`, whose identity is $Q$, and $\rho$ is a `MulEquiv` (a multiplicative bijection, hence a monoid isomorphism). The statement asserts the existence of the idempotence proof `hQ` together with $\rho$. No finiteness of $H$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/RelationMonoid.lean#L157-L226

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.relation_corner_equiv {H : Type*} (P : SetRel H H) (F : Set H)
    (hP : P ○ P = P) (hiPi : restrictedIdentity F ○ P ○ restrictedIdentity F =
      restrictedIdentity F) :
    ∃ hQ : IsIdempotentElem (RelationMonoid.ofRel (P ○ restrictedIdentity F ○ P)),
      ∃ ρ : hQ.Corner ≃* RelationMonoid F,
        ∀ Z, (ρ Z).toRel = {xy : F × F | (xy.1.val, xy.2.val) ∈ Z.val.toRel} := by sorry
