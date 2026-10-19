-- Prove2me | Theorems.Thm_OAI_CHObstruction_Tuples_cardinal_bound
-- name    : OAI.CHObstruction.Tuples.cardinal_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:00:41.877989+00:00
-- url     : https://prove2.me/theorems/b7e291c6-dd4d-4ee9-88af-98be5cf26e21
-- title:
--   At most $\kappa$ finite injective tuples over a set of size at most $\kappa$
-- statement:
--   Let $I$ be a set and let $\mathrm{Tup}(I)$ be the set of nonempty finite injective sequences in $I$,
--   $$\mathrm{Tup}(I)=\bigsqcup_{n\in\mathbb N}\{\,t:\{0,1,\dots,n\}\to I\ \text{ injective}\,\}.$$
--   If $\kappa$ is an infinite cardinal ($\aleph_0\le\kappa$) and $|I|\le\kappa$, then
--
--   $$
--   |\mathrm{Tup}(I)|\le\kappa .
--   $$
--
--   Tuples index the rows and columns of the arrays in the categoricity construction, so this bound enters every estimate of the size of an array (its point set and the number of test conditions attached to its tuples), in particular in the downward Löwenheim–Skolem argument.
--
--   **Formalization Note** `Tuple I` is the sigma type `Σ n : ℕ, Fin (n + 1) ↪ I` of embeddings; $\kappa$ is a cardinal in the universe of $I$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/Arrays.lean#L185-L200

import Mathlib
import Definitions.Def_CHObstruction
import Definitions.Def_OAI_ModelTheory_Categoricity_Collapse
import Definitions.Def_OAI_ModelTheory_Categoricity_Diagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_Partition
import Definitions.Def_OAI_ModelTheory_Categoricity_Colors
import Definitions.Def_OAI_ModelTheory_Categoricity_EndpointDiagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_TailBound
import Definitions.Def_OAI_ModelTheory_Categoricity_Arrays

open OAI OAI.CHObstruction OAI.CHObstruction.Tuples
universe u v w
open Cardinal Ordinal Order
variable {I J K : Type u}

theorem OAI.CHObstruction.Tuples.cardinal_bound (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hI : #I ≤ κ) : #(Tuple I) ≤ κ := by sorry
