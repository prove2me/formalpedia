-- Prove2me | Theorems.Thm_OAI_Thorp_Young_extensions_card_ideal
-- name    : OAI.Thorp.Young.extensions_card_ideal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:24:21.171363+00:00
-- url     : https://prove2.me/theorems/c2366ef0-6685-4a2b-9f14-fd639bec98b6
-- title:
--   A down-set of a finite poset has at most as many linear extensions as the poset
-- statement:
--   Let $A$ be a finite partially ordered set with $N=|A|$ elements. A *linear extension* of $A$ is a bijection $\lambda:A\to\{0,1,\dots,N-1\}$ that is strictly order-preserving: $x<y$ implies $\lambda(x)<\lambda(y)$. Write $e(A)$ for the number of linear extensions of $A$; a subset of $A$ is regarded as a poset with the induced order. Let $s\subseteq A$ be a down-set (lower set): whenever $y\in s$ and $x\le y$, also $x\in s$. Then
--
--   $$
--   e(s)\le e(A).
--   $$
--
--   The number of linear extensions is thus monotone under passing to order ideals. For the cell poset of a Young diagram, linear extensions are standard Young tableaux and down-sets are smaller Young diagrams, so the inequality allows one to shrink a diagram while keeping a lower bound on the number of standard tableaux of the original shape.
--
--   **Formalization Note** $e(A)$ is `Fintype.card (Extensions A)`, where `Extensions A` is the type of equivalences `A ≃ Fin (Fintype.card A)` that are `StrictMono`; the down-set hypothesis is `IsLowerSet s` and `Extensions s` refers to the subtype `s` with the induced partial order.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/ExtensionBounds.lean#L16-L49

import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification
import Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions
import Definitions.Def_OAI_Probability_ThorpShuffle_ExtensionBounds

open OAI OAI.Thorp OAI.Thorp.Young
universe uA
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter
open scoped Classical
variable {A : Type uA} [Fintype A] [PartialOrder A]

theorem OAI.Thorp.Young.extensions_card_ideal (s : Set A) (hs : IsLowerSet s) :
    Fintype.card (Extensions s) ≤ Fintype.card (Extensions A) := by sorry
