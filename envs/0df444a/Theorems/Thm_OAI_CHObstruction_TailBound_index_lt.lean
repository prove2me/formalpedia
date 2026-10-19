-- Prove2me | Theorems.Thm_OAI_CHObstruction_TailBound_index_lt
-- name    : OAI.CHObstruction.TailBound.index_lt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:57:37.759057+00:00
-- url     : https://prove2.me/theorems/0bfa5d12-7340-49c4-9833-51822980ef18
-- title:
--   Under CH, few test failures over an uncountable base force fewer than $\beth_{(2^{\aleph_1})^+}$ indices
-- statement:
--   Assume CH, $2^{\aleph_0}=\aleph_1$. Let $\mathcal C$ (the *palette*) be the set of binary sequences $a:\mathbb N\to\{0,1\}$ modulo the equivalence relation of differing in only finitely many places, and write $[a]\in\mathcal C$ for the class of $a$. For a set $I$, $\mathrm{Tup}(I)$ is the set of *tuples* in $I$, i.e. injective maps $t:\{0,\dots,n\}\to I$ with $n\in\mathbb N$ (of length $n+1$); for a strictly increasing $e:\{0,\dots,m\}\to\{0,\dots,n\}$ the tuple $t\circ e$ is a *subtuple* of $t$, and an injection $h:I\to I'$ sends $t$ to $h\circ t\in\mathrm{Tup}(I')$.
--
--   A *label* on a set $A$ is a pair $(F,k)$ with $F\subseteq A$ finite and nonempty and $k\in\mathbb N$. A *diagram* $d$ on $A$ consists of two binary relations $\equiv_d$ and $\triangleleft_d$ on labels and a *tag* map $\tau_d$ from labels to countable ordinals. It is *valid* if $\equiv_d$ is an equivalence relation, $\triangleleft_d$ and $\tau_d$ are invariant under $\equiv_d$, $x\triangleleft_d y$ implies $\tau_d(x)<\tau_d(y)$, two labels with the same $\triangleleft_d$-predecessors are $\equiv_d$-equivalent, and $(\{a\},0)\equiv_d(\{b\},0)$ only when $a=b$. A diagram $d$ on $A'$ *restricts* along an injection $e:A\to A'$ to the diagram $d|_e$ on $A$ obtained by pulling $\equiv_d$, $\triangleleft_d$ and $\tau_d$ back along $(F,k)\mapsto(e[F],k)$. Under CH each finite set carries at most $2^{\aleph_0}$ diagrams, and $\mathrm{code}$ denotes a fixed injection of the set of pairs $(m,d)$, with $d$ a diagram on $\{0,\dots,m\}$, into $\mathcal C$. For a coloring $c:\mathrm{Tup}(I)\to\mathcal C$ and a tuple $t$ of length $n+1$, the *diagram test* $\mathsf T(c,t)$ asserts that there is a diagram $d$ on $\{0,\dots,n\}$ such that for every $m$ and every strictly increasing $e:\{0,\dots,m\}\to\{0,\dots,n\}$ the restriction $d|_e$ is valid and $\mathrm{code}(m,d|_e)=c(t\circ e)$.
--
--   **Theorem.** Let $I$ and $B$ be sets such that $B$ is uncountable and $|B|\le\aleph_1$, and let $c:\mathrm{Tup}(I)\times B\to\mathcal C$. Assume that for every tuple $t\in\mathrm{Tup}(I)$ the set $\{b\in B:\ \mathsf T(c(\cdot,b),t)\text{ fails}\}$ is countable. Then
--
--   $$
--   |I|<\beth_{(2^{\aleph_1})^+},
--   $$
--
--   where the index of the beth function is the initial ordinal of the successor cardinal of $2^{\aleph_1}$.
--
--   In the categoricity construction this is applied with $B$ the base order of an array and $c(t,b)$ the color of the column of $t$ at $b$; it bounds the index set of every array object with uncountable base. The cardinal $\beth_{(2^{\aleph_1})^+}$ is the threshold from which on the main theorem asserts categoricity.
--
--   **Formalization Note** The cardinal $\beth_{(2^{\aleph_1})^+}$ is `tailThreshold`, defined as `beth (succ (2 ^ ℵ_ 1)).ord`; the coloring is curried as `c : Tuple I → B → Palette`, the test is `Test hCH (fun t => c t b) t`, and uncountability is `¬ Countable B`. The sets $I$, $B$ are types of a fixed universe, in which CH is stated as `(2 : Cardinal) ^ ℵ₀ = ℵ_ 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/TailBound.lean#L90-L122

import Mathlib
import Definitions.Def_CHObstruction
import Definitions.Def_OAI_ModelTheory_Categoricity_Collapse
import Definitions.Def_OAI_ModelTheory_Categoricity_Diagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_Partition
import Definitions.Def_OAI_ModelTheory_Categoricity_Colors
import Definitions.Def_OAI_ModelTheory_Categoricity_EndpointDiagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_TailBound

open OAI OAI.CHObstruction
universe u v w
open Cardinal Ordinal Order
open Tuples Diagrams Colors Tests ThresholdArithmetic
variable {I B : Type u} (hCH : CH.{u})

theorem OAI.CHObstruction.TailBound.index_lt (hB : #B ≤ (ℵ_ 1 : Cardinal.{u})) (hunc : ¬ Countable B)
    (c : Tuple I → B → Palette.{u})
    (hbad : ∀ t, {b | ¬ Test hCH (fun t => c t b) t}.Countable) :
    #I < tailThreshold.{u} := by sorry
