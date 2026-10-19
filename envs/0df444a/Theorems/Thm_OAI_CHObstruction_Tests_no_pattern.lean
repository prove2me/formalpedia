-- Prove2me | Theorems.Thm_OAI_CHObstruction_Tests_no_pattern
-- name    : OAI.CHObstruction.Tests.no_pattern
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:56:50.857237+00:00
-- url     : https://prove2.me/theorems/82e7c298-73ea-4d9f-a27f-12f7fc61a025
-- title:
--   Under CH no color sequence passes the diagram test in every finite dimension
-- statement:
--   Assume the continuum hypothesis (CH), $2^{\aleph_0}=\aleph_1$. Let $\mathcal C$ (the *palette*) be the set of binary sequences $a:\mathbb N\to\{0,1\}$ modulo the equivalence relation of differing in only finitely many places, and write $[a]\in\mathcal C$ for the class of $a$.
--
--   A *label* on a set $A$ is a pair $(F,k)$ with $F\subseteq A$ finite and nonempty and $k\in\mathbb N$. A *diagram* $d$ on $A$ consists of two binary relations $\equiv_d$ and $\triangleleft_d$ on labels and a *tag* map $\tau_d$ from labels to countable ordinals. It is *valid* if $\equiv_d$ is an equivalence relation, $\triangleleft_d$ and $\tau_d$ are invariant under $\equiv_d$, $x\triangleleft_d y$ implies $\tau_d(x)<\tau_d(y)$, two labels with the same $\triangleleft_d$-predecessors are $\equiv_d$-equivalent, and $(\{a\},0)\equiv_d(\{b\},0)$ only when $a=b$. A diagram $d$ on $A'$ *restricts* along an injection $e:A\to A'$ to the diagram $d|_e$ on $A$ obtained by pulling $\equiv_d$, $\triangleleft_d$ and $\tau_d$ back along $(F,k)\mapsto(e[F],k)$. Under CH each finite set carries at most $2^{\aleph_0}$ diagrams, and $\mathrm{code}$ denotes a fixed injection of the set of pairs $(m,d)$, with $d$ a diagram on $\{0,\dots,m\}$, into $\mathcal C$.
--
--   **Theorem.** For every sequence $(p_m)_{m\in\mathbb N}$ in $\mathcal C$ the following is false: for every $n\in\mathbb N$ there is a diagram $d$ on $\{0,\dots,n\}$ such that
--
--   $$
--   d|_e\ \text{is valid}\quad\text{and}\quad \mathrm{code}(m,d|_e)=p_m\qquad\text{for all } m\in\mathbb N\text{ and all strictly increasing } e:\{0,\dots,m\}\to\{0,\dots,n\}.
--   $$
--
--   Say that a coloring $c$ of finite injective tuples *passes the diagram test* at an injective tuple $t:\{0,\dots,n\}\to I$ when some diagram $d$ on $\{0,\dots,n\}$ has every restriction $d|_e$, for $e:\{0,\dots,m\}\to\{0,\dots,n\}$ strictly increasing, valid with $\mathrm{code}(m,d|_e)=c(t\circ e)$. The theorem says that a coloring giving all tuples of length $m+1$ one and the same color $p_m$, for every $m$, cannot pass the test at tuples of every length. It is the obstruction used to bound the number of indices of array objects with uncountable base: a large homogeneous set of indices would produce exactly such a sequence.
--
--   **Formalization Note** The hypothesis is `∀ n, Passes hCH (n := n) (fun m _ => p m)`; `Passes` quantifies over order embeddings `Fin (m + 1) ↪o Fin (n + 1)`, diagrams are `Diagram (Fin (n + 1))` with tags in `(ω_ 1).ToType`, and the palette is `Palette = ULift Color`. The injection `code hCH : (Σ n, Diagram (Fin (n + 1))) ↪ Palette` is obtained by `Classical.choice` from the cardinality bound under CH, which is stated in a fixed universe as `(2 : Cardinal) ^ ℵ₀ = ℵ_ 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/Colors.lean#L173-L201

import Mathlib
import Definitions.Def_CHObstruction
import Definitions.Def_OAI_ModelTheory_Categoricity_Collapse
import Definitions.Def_OAI_ModelTheory_Categoricity_Diagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_Partition
import Definitions.Def_OAI_ModelTheory_Categoricity_Colors

open OAI OAI.CHObstruction OAI.CHObstruction.Tests
universe u v w
open Cardinal Ordinal Order
open Diagrams Colors Tuples
variable (hCH : CH.{u})

theorem OAI.CHObstruction.Tests.no_pattern (p : ℕ → Palette.{u})
    (hp : ∀ n : ℕ, Passes hCH (n := n) (fun m _ => p m)) : False := by sorry
