-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_conditional_card_event
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.conditional_card_event
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:24:36.536024+00:00
-- url     : https://prove2.me/theorems/cf6f18f6-6a5b-4777-beff-62259caa9633
-- title:
--   A second independent linear functional is equidistributed on each fiber of the first
-- statement:
--   Let $K$ be a field and $V$ a vector space over $K$ with finitely many elements. Let $f,g:V\to K$ be linear functionals such that the joint map $v\mapsto(f(v),g(v))$ from $V$ to $K^2$ is surjective (equivalently, $f$ and $g$ are linearly independent). Then for every $s\in K$ and every finite set $S\subseteq K$,
--
--   $$
--   \big|\{v\in V:\ f(v)=s,\ g(v)\in S\}\big|\;=\;|S|\cdot\big|\{v\in V:\ f(v)=s,\ g(v)=0\}\big| .
--   $$
--
--   In other words, on the fiber $\{f=s\}$ the value $g(v)$ is uniformly distributed over $K$: every value of $g$ is taken equally often, so a uniformly random vector with $f(v)=s$ has $g(v)\in S$ with probability $|S|/|K|$. This is used to compute conditional hitting probabilities for pairs of linear forms over finite fields in the random slot construction.
--
--   **Formalization Note** The fiber $\{v: f(v)=s\}$ is `fiber f s`, the finset of all $v$ with $f(v)=s$, and the joint map is `f.prod g`. The field is not separately assumed finite in this statement (the instance `Fintype K` is omitted); finiteness of $K$ follows from the surjectivity of $(f,g)$ and the finiteness of $V$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/FiniteRank.lean#L160-L182

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

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
universe uK uV uι uW uJ
open scoped BigOperators
open Finset
variable {K : Type uK} {V : Type uV} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

omit [Fintype K] [DecidableEq V] in
theorem OAI.AsymptoticallyMinimalLittlewood.Packing.conditional_card_event (f g : V →ₗ[K] K)
    (hfg : Function.Surjective (f.prod g)) (s : K) (S : Finset K) :
    ((fiber f s).filter (fun v ↦ g v∈S)).card =
      S.card*((fiber f s).filter (fun v ↦ g v=0)).card := by sorry
