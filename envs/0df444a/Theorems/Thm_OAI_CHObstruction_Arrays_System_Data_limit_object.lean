-- Prove2me | Theorems.Thm_OAI_CHObstruction_Arrays_System_Data_limit_object
-- name    : OAI.CHObstruction.Arrays.System.Data.limit_object
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:16:13.982904+00:00
-- url     : https://prove2.me/theorems/f7145724-1774-4c93-808b-555e3c82947a
-- title:
--   The limit of a directed system of array objects along strong maps is an object
-- statement:
--   Assume CH, $2^{\aleph_0}=\aleph_1$. Let $\mathcal C$ (the *palette*) be the set of binary sequences $a:\mathbb N\to\{0,1\}$ modulo the equivalence relation of differing in only finitely many places, and write $[a]\in\mathcal C$ for the class of $a$. For a set $I$, $\mathrm{Tup}(I)$ is the set of *tuples* in $I$, i.e. injective maps $t:\{0,\dots,n\}\to I$ with $n\in\mathbb N$ (of length $n+1$); for a strictly increasing $e:\{0,\dots,m\}\to\{0,\dots,n\}$ the tuple $t\circ e$ is a *subtuple* of $t$, and an injection $h:I\to I'$ sends $t$ to $h\circ t\in\mathrm{Tup}(I')$.
--
--   For a coloring $c:\mathrm{Tup}(I)\to\mathcal C$ and a tuple $t$ of length $n+1$, the *diagram test* $\mathsf T(c,t)$ asserts that there is a diagram $d$ on $\{0,\dots,n\}$ (two relations $\equiv_d$, $\triangleleft_d$ on labels $(F,k)$, where $F\subseteq\{0,\dots,n\}$ is finite nonempty and $k\in\mathbb N$, together with countable-ordinal tags) such that for every strictly increasing $e:\{0,\dots,m\}\to\{0,\dots,n\}$ the restricted diagram $d|_e$ is valid and $\mathrm{code}(m,d|_e)=c(t\circ e)$. Here *valid* means that $\equiv_d$ is an equivalence relation compatible with $\triangleleft_d$ and the tags, tags strictly increase along $\triangleleft_d$, labels with the same $\triangleleft_d$-predecessors are equivalent, and the root labels $(\{a\},0)$ of distinct points are inequivalent; $\mathrm{code}$ is a fixed injection of diagrams on finite sets into $\mathcal C$, which exists under CH. In particular $\mathsf T(c,t)$ depends only on the colors $c(t\circ e)$ of the subtuples of $t$.
--
--   An *array* $M$ consists of a nonempty set $I_M$ of *indices*, a nonempty set $B_M$ of *base points* carrying a dense linear order without endpoints in which every closed interval is countable, and a *bit matrix* $\beta_M:\mathrm{Tup}(I_M)\times\mathbb N\times B_M\to\{0,1\}$. The set $\mathrm{Pts}(M)$ of *points* of $M$ is the disjoint union of six sorts: index points $i\in I_M$; base points $b\in B_M$; group points, one for each finite $s\subseteq B_M$; star points, one for each finite $v\subseteq\mathbb N$; row points $(t,n,s)$ with $t\in\mathrm{Tup}(I_M)$, $n\in\mathbb N$ and finite $s\subseteq B_M$; and column points $(t,b,v)$ with $t\in\mathrm{Tup}(I_M)$, $b\in B_M$ and finite $v\subseteq\mathbb N$. The *column color* of $t\in\mathrm{Tup}(I_M)$ at $b\in B_M$ is $\chi_M(t,b)=[\,n\mapsto\beta_M(t,n,b)\,]\in\mathcal C$, and $M$ is an *object* if for every $t\in\mathrm{Tup}(I_M)$ only countably many $b\in B_M$ fail the test $\mathsf T(\chi_M(\cdot,b),t)$.
--
--   A *map* $f:M\to N$ of arrays consists of an injection $f_I:I_M\to I_N$, an order embedding $f_B:B_M\to B_N$, finite *row shifts* $\rho_f(t,n)\subseteq B_N$ and finite *column shifts* $\gamma_f(t,b)\subseteq\mathbb N$ ($t\in\mathrm{Tup}(I_M)$, $n\in\mathbb N$, $b\in B_M$) satisfying the bit identity
--   $$\beta_N(f_I\circ t,n,f_Bb)\oplus[f_Bb\in\rho_f(t,n)]\oplus[n\in\gamma_f(t,b)]=\beta_M(t,n,b),$$
--   where $\oplus$ is exclusive or and $[\,\cdot\,]\in\{0,1\}$ is the truth value of a statement. The composite of $f:M\to N$ and $g:N\to P$ is the map $g\circ f$ with components $g_I\circ f_I$, $g_B\circ f_B$, $\rho_{g\circ f}(t,n)=\rho_g(f_I\circ t,n)\mathbin{\triangle}g_B[\rho_f(t,n)]$ and $\gamma_{g\circ f}(t,b)=\gamma_g(f_I\circ t,f_Bb)\mathbin{\triangle}\gamma_f(t,b)$, where $\triangle$ is symmetric difference. For a map $f:M\to N$, a tuple $t\in\mathrm{Tup}(I_M)$ and a base point $b\in B_N$ of the target, the *twisted color* is
--   $$\chi_f(t,b)=\bigl[\,n\mapsto\beta_N(f_I\circ t,n,b)\oplus[b\in\rho_f(t,n)]\,\bigr]\in\mathcal C .$$ A map $f:M\to N$ is *strong* if the range of $f_B$ is order-convex in $B_N$ (whenever $f_Ba\le z\le f_Bc$, also $z\in f_B[B_M]$) and $\mathsf T(\chi_f(\cdot,b),t)$ holds for every $t\in\mathrm{Tup}(I_M)$ and every $b\in B_N$ outside the range of $f_B$.
--
--   Let $J$ be a nonempty directed preordered set. A *directed system of arrays* over $J$ consists of arrays $M_i$ ($i\in J$) and maps $f_{ij}:M_i\to M_j$ ($i\le j$) with $f_{ii}=\mathrm{id}$ (identity components, empty shifts) and $f_{jk}\circ f_{ij}=f_{ik}$ for $i\le j\le k$. Assume moreover that the range of every base embedding $(f_{ij})_B$ is order-convex. Then the system has a *limit array* $M_\infty$: its index set is the direct limit $I_\infty=\varinjlim_i I_{M_i}$, its base is the direct limit $B_\infty=\varinjlim_i B_{M_i}$ with the induced linear order (dense, without endpoints, and with countable closed intervals thanks to the convexity assumption), and its bit matrix is induced from those of the $M_i$ through the direct limit of their point sets. The *canonical maps* $f_{i\infty}:M_i\to M_\infty$ have as index and base components the canonical maps into the two direct limits and satisfy $f_{j\infty}\circ f_{ij}=f_{i\infty}$ for $i\le j$; every point of $M_\infty$ is the image of a point of some $M_i$.
--
--   **Theorem.** In this situation, if every $M_i$ is an object and every transition map $f_{ij}$ ($i\le j$) is strong, then the limit array is an object:
--
--   $$
--   \bigl(\forall i:\ M_i\ \text{object}\bigr)\ \wedge\ \bigl(\forall\, i\le j:\ f_{ij}\ \text{strong}\bigr)\quad\Longrightarrow\quad M_\infty\ \text{object}.
--   $$
--
--   So the class of array objects is closed under limits of strong directed systems; this is the membership half of the union axiom for the abstract elementary class built from arrays.
--
--   **Formalization Note** The system is `System.Data` (fields `obj`, `map`, `map_id`, `map_comp`), the convexity hypothesis is `hconv`, which is needed to build the limit array `limitData hconv` (it makes the closed intervals of the limit base countable), and the canonical maps are `toLimit hconv i`. The bit matrix of the limit is defined through chosen origin row and column points of the direct limit of the point sets, and the shifts of `toLimit` record the differences from these origins.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/DirectedLimits.lean#L918-L940

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
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayIsomorphisms
import Definitions.Def_OAI_ModelTheory_Categoricity_DirectedLimits

open OAI OAI.CHObstruction OAI.CHObstruction.Arrays OAI.CHObstruction.Arrays.System OAI.CHObstruction.Arrays.System.Data
universe u v w
open Cardinal Ordinal Order
attribute [local instance] OAI.CHObstruction.Arrays.System.Data.instDecidableEqB
attribute [local instance] OAI.CHObstruction.Arrays.System.Data.instDecidableEqBObj
attribute [local instance] OAI.CHObstruction.Arrays.System.Data.instDecidableEqTupleIObj
variable {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]
open Tuples
variable (S : Data (J := J))
open scoped symmDiff
variable (hconv : ∀ i j (h : i ≤ j), Set.OrdConnected (Set.range (S.map i j h).base))
variable {hCH : CH.{u}}

theorem OAI.CHObstruction.Arrays.System.Data.limit_object (hobj : ∀ i, (S.obj i).IsObject hCH)
    (hstrong : ∀ i j h, (S.map i j h).Strong hCH) :
    (S.limitData hconv).IsObject hCH := by sorry
