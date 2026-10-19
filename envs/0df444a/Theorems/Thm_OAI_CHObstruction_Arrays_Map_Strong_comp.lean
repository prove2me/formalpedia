-- Prove2me | Theorems.Thm_OAI_CHObstruction_Arrays_Map_Strong_comp
-- name    : OAI.CHObstruction.Arrays.Map.Strong.comp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:01:49.789749+00:00
-- url     : https://prove2.me/theorems/a60ef9de-140a-42ce-b410-9d208d0db88c
-- title:
--   Composites of strong array maps are strong
-- statement:
--   Assume CH, $2^{\aleph_0}=\aleph_1$. Let $\mathcal C$ (the *palette*) be the set of binary sequences $a:\mathbb N\to\{0,1\}$ modulo the equivalence relation of differing in only finitely many places, and write $[a]\in\mathcal C$ for the class of $a$. For a set $I$, $\mathrm{Tup}(I)$ is the set of *tuples* in $I$, i.e. injective maps $t:\{0,\dots,n\}\to I$ with $n\in\mathbb N$ (of length $n+1$); for a strictly increasing $e:\{0,\dots,m\}\to\{0,\dots,n\}$ the tuple $t\circ e$ is a *subtuple* of $t$, and an injection $h:I\to I'$ sends $t$ to $h\circ t\in\mathrm{Tup}(I')$.
--
--   For a coloring $c:\mathrm{Tup}(I)\to\mathcal C$ and a tuple $t$ of length $n+1$, the *diagram test* $\mathsf T(c,t)$ asserts that there is a diagram $d$ on $\{0,\dots,n\}$ (two relations $\equiv_d$, $\triangleleft_d$ on labels $(F,k)$, where $F\subseteq\{0,\dots,n\}$ is finite nonempty and $k\in\mathbb N$, together with countable-ordinal tags) such that for every strictly increasing $e:\{0,\dots,m\}\to\{0,\dots,n\}$ the restricted diagram $d|_e$ is valid and $\mathrm{code}(m,d|_e)=c(t\circ e)$. Here *valid* means that $\equiv_d$ is an equivalence relation compatible with $\triangleleft_d$ and the tags, tags strictly increase along $\triangleleft_d$, labels with the same $\triangleleft_d$-predecessors are equivalent, and the root labels $(\{a\},0)$ of distinct points are inequivalent; $\mathrm{code}$ is a fixed injection of diagrams on finite sets into $\mathcal C$, which exists under CH. In particular $\mathsf T(c,t)$ depends only on the colors $c(t\circ e)$ of the subtuples of $t$.
--
--   An *array* $M$ consists of a nonempty set $I_M$ of *indices*, a nonempty set $B_M$ of *base points* carrying a dense linear order without endpoints in which every closed interval is countable, and a *bit matrix* $\beta_M:\mathrm{Tup}(I_M)\times\mathbb N\times B_M\to\{0,1\}$. A *map* $f:M\to N$ of arrays consists of an injection $f_I:I_M\to I_N$, an order embedding $f_B:B_M\to B_N$, finite *row shifts* $\rho_f(t,n)\subseteq B_N$ and finite *column shifts* $\gamma_f(t,b)\subseteq\mathbb N$ ($t\in\mathrm{Tup}(I_M)$, $n\in\mathbb N$, $b\in B_M$) satisfying the bit identity
--   $$\beta_N(f_I\circ t,n,f_Bb)\oplus[f_Bb\in\rho_f(t,n)]\oplus[n\in\gamma_f(t,b)]=\beta_M(t,n,b),$$
--   where $\oplus$ is exclusive or and $[\,\cdot\,]\in\{0,1\}$ is the truth value of a statement. The composite of $f:M\to N$ and $g:N\to P$ is the map $g\circ f$ with components $g_I\circ f_I$, $g_B\circ f_B$, $\rho_{g\circ f}(t,n)=\rho_g(f_I\circ t,n)\mathbin{\triangle}g_B[\rho_f(t,n)]$ and $\gamma_{g\circ f}(t,b)=\gamma_g(f_I\circ t,f_Bb)\mathbin{\triangle}\gamma_f(t,b)$, where $\triangle$ is symmetric difference.
--
--   For a map $f:M\to N$, a tuple $t\in\mathrm{Tup}(I_M)$ and a base point $b\in B_N$ of the target, the *twisted color* is
--   $$\chi_f(t,b)=\bigl[\,n\mapsto\beta_N(f_I\circ t,n,b)\oplus[b\in\rho_f(t,n)]\,\bigr]\in\mathcal C .$$ A map $f:M\to N$ is *strong* if the range of $f_B$ is order-convex in $B_N$ (whenever $f_Ba\le z\le f_Bc$, also $z\in f_B[B_M]$) and $\mathsf T(\chi_f(\cdot,b),t)$ holds for every $t\in\mathrm{Tup}(I_M)$ and every $b\in B_N$ outside the range of $f_B$.
--
--   **Theorem.** Let $f:M\to N$ and $g:N\to P$ be maps of arrays. Then
--
--   $$
--   f\ \text{strong and}\ g\ \text{strong}\quad\Longrightarrow\quad g\circ f\ \text{strong}.
--   $$
--
--   Strong maps realize the strong-substructure relation of the abstract elementary class built from arrays, and closure under composition gives the transitivity of that relation; it is also used to move strong maps between different array presentations of the same structure.
--
--   **Formalization Note** Strongness is the structure `Map.Strong hCH f` with fields `convex` (`Set.OrdConnected (Set.range f.base)`) and `outside`; the test is `Tests.Test hCH` and $\chi_f$ is `Map.colors f`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/ArrayEmbeddings.lean#L136-L158

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

open OAI OAI.CHObstruction OAI.CHObstruction.Arrays
universe u v w
open Cardinal Ordinal Order
open Tuples
open scoped symmDiff
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_8
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_9
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_10
variable {M N P : Data.{u}}

theorem OAI.CHObstruction.Arrays.Map.Strong.comp (hCH : CH.{u}) {g : Map N P} {f : Map M N}
    (hg : g.Strong hCH) (hf : f.Strong hCH) : (g.comp f).Strong hCH := by sorry
