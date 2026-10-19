-- Prove2me | Theorems.Thm_OAI_CHObstruction_BaseOrders_small_hull
-- name    : OAI.CHObstruction.BaseOrders.small_hull
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:05:31.569161+00:00
-- url     : https://prove2.me/theorems/ac98e3d0-c13d-4f14-8211-f369a23586f1
-- title:
--   Small convex dense hulls in a locally countable dense linear order
-- statement:
--   Let $(B,\le)$ be a nonempty dense linear order without least or greatest element in which every closed interval $[a,b]$, $a,b\in B$, is countable. Let $A\subseteq B$ and let $\kappa$ be an infinite cardinal with $|A|\le\kappa$. Then there is a set $S$ with
--
--   $$
--   A\subseteq S\subseteq B,\qquad |S|\le\kappa,
--   $$
--
--   such that
--   1. $S$ is order-convex in $B$: if $x,y\in S$ and $x\le z\le y$, then $z\in S$;
--   2. $S$ is nonempty;
--   3. with the induced order, $S$ has no least and no greatest element;
--   4. with the induced order, $S$ is dense.
--
--   So every subset of a base order of an array can be enlarged, within the same infinite size bound, to a convex subset that is again a legitimate base order (nonempty, dense, without endpoints, and locally countable, the last property being inherited from $B$). This is the order-theoretic step of the downward Löwenheim–Skolem argument for arrays, where the base of a small subarray must be convex for the inclusion map to be strong.
--
--   **Formalization Note** Convexity is `Set.OrdConnected S`, and items 2–4 are the instances `Nonempty S`, `NoMinOrder S`, `NoMaxOrder S` and `DenselyOrdered S` on the subtype; $|S|$ is `#S`, a cardinal in the universe of $B$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/Subarrays.lean#L18-L65

import Mathlib
import Definitions.Def_CHObstruction
import Definitions.Def_OAI_ModelTheory_Categoricity_Collapse
import Definitions.Def_OAI_ModelTheory_Categoricity_Diagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_Partition
import Definitions.Def_OAI_ModelTheory_Categoricity_Colors
import Definitions.Def_OAI_ModelTheory_Categoricity_EndpointDiagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_TailBound
import Definitions.Def_OAI_ModelTheory_Categoricity_Arrays
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayMaps
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayEmbeddings
import Definitions.Def_OAI_ModelTheory_Categoricity_Subarrays

open OAI OAI.CHObstruction
universe u v w
open Cardinal Ordinal Order
variable {B : Type u} [LinearOrder B] [DenselyOrdered B] [NoMinOrder B]
  [NoMaxOrder B] [Nonempty B]

theorem OAI.CHObstruction.BaseOrders.small_hull (loc : ∀ a b : B, (Set.Icc a b).Countable)
    (A : Set B) (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) :
    ∃ S : Set B, A ⊆ S ∧ S.OrdConnected ∧ Nonempty S ∧
      NoMinOrder S ∧ NoMaxOrder S ∧ DenselyOrdered S ∧ #S ≤ κ := by sorry
