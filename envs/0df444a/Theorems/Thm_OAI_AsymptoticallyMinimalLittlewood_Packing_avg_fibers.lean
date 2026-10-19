-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_avg_fibers
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.avg_fibers
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:32:06.084719+00:00
-- url     : https://prove2.me/theorems/b5ea1b95-f24a-42a2-b428-4b25319e65e8
-- title:
--   Averaging over the fibers of a surjective linear functional
-- statement:
--   For a nonempty finite set $X$ and $h:X\to\mathbb R$ write $\operatorname{avg}_{x\in X}h(x)=\frac1{|X|}\sum_{x\in X}h(x)$.
--
--   Let $K$ be a finite field, $V$ a vector space over $K$ with finitely many elements, $f:V\to K$ a surjective linear functional, and $F:V\to\mathbb R$ any function. For $s\in K$ let $f^{-1}(s)=\{v\in V: f(v)=s\}$. Then
--
--   $$
--   \operatorname{avg}_{s\in K}\ \operatorname{avg}_{v\in f^{-1}(s)}F(v)=\operatorname{avg}_{v\in V}F(v).
--   $$
--
--   This is the law of total expectation for the partition of $V$ into the fibers of $f$, which all have the same size: a uniformly random vector can be sampled by first choosing the value $s=f(v)$ uniformly in $K$ and then choosing $v$ uniformly in the fiber $f^{-1}(s)$. It is used to pass between averages over the residue $s$ and averages over the whole space in the random slot construction.
--
--   **Formalization Note** The fiber is `fiber f s`, a finset, and the inner average is taken over the corresponding subtype. `avg h` is the sum of $h$ divided by the cardinality of its finite domain.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/DependentMoments.lean#L161-L178

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
universe uκ uA uJ uY uV uK uΩ uI
open scoped BigOperators
open Finset
variable {K : Type uK} {V : Type uV} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem OAI.AsymptoticallyMinimalLittlewood.Packing.avg_fibers (f : V →ₗ[K] K) (hf : Function.Surjective f) (F : V → ℝ) :
    avg (fun s : K ↦ avg (fun v : fiber f s ↦ F v))=avg F := by sorry
