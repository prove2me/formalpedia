-- Prove2me | Theorems.Thm_OAI_CHObstruction_Arrays_Map_factor
-- name    : OAI.CHObstruction.Arrays.Map.factor
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:10:24.548988+00:00
-- url     : https://prove2.me/theorems/ac4a07bd-7738-4be8-82a7-debb6e0e695c
-- title:
--   An array map whose image lies in the image of another map factors through it
-- statement:
--   For a set $I$, $\mathrm{Tup}(I)$ is the set of *tuples* in $I$, i.e. injective maps $t:\{0,\dots,n\}\to I$ with $n\in\mathbb N$ (of length $n+1$); for a strictly increasing $e:\{0,\dots,m\}\to\{0,\dots,n\}$ the tuple $t\circ e$ is a *subtuple* of $t$, and an injection $h:I\to I'$ sends $t$ to $h\circ t\in\mathrm{Tup}(I')$.
--
--   An *array* $M$ consists of a nonempty set $I_M$ of *indices*, a nonempty set $B_M$ of *base points* carrying a dense linear order without endpoints in which every closed interval is countable, and a *bit matrix* $\beta_M:\mathrm{Tup}(I_M)\times\mathbb N\times B_M\to\{0,1\}$. The set $\mathrm{Pts}(M)$ of *points* of $M$ is the disjoint union of six sorts: index points $i\in I_M$; base points $b\in B_M$; group points $s$, one for each finite $s\subseteq B_M$; star points $v$, one for each finite $v\subseteq\mathbb N$; row points $(t,n,s)$ with $t\in\mathrm{Tup}(I_M)$, $n\in\mathbb N$ and finite $s\subseteq B_M$; and column points $(t,b,v)$ with $t\in\mathrm{Tup}(I_M)$, $b\in B_M$ and finite $v\subseteq\mathbb N$.
--
--   A *map* $f:M\to N$ of arrays consists of an injection $f_I:I_M\to I_N$, an order embedding $f_B:B_M\to B_N$, finite *row shifts* $\rho_f(t,n)\subseteq B_N$ and finite *column shifts* $\gamma_f(t,b)\subseteq\mathbb N$ ($t\in\mathrm{Tup}(I_M)$, $n\in\mathbb N$, $b\in B_M$) satisfying the bit identity
--   $$\beta_N(f_I\circ t,n,f_Bb)\oplus[f_Bb\in\rho_f(t,n)]\oplus[n\in\gamma_f(t,b)]=\beta_M(t,n,b),$$
--   where $\oplus$ is exclusive or and $[\,\cdot\,]\in\{0,1\}$ is the truth value of a statement. A map $f$ acts on points by $\hat f(i)=f_I(i)$, $\hat f(b)=f_B(b)$, $\hat f(s)=f_B[s]$ on group points, $\hat f(v)=v$ on star points,
--   $$\hat f(t,n,s)=\bigl(f_I\circ t,\ n,\ \rho_f(t,n)\mathbin{\triangle}f_B[s]\bigr),\qquad \hat f(t,b,v)=\bigl(f_I\circ t,\ f_Bb,\ \gamma_f(t,b)\mathbin{\triangle}v\bigr)$$
--   on row and column points, where $\triangle$ is symmetric difference; the point map $\hat f$ is always injective. The composite of $f:M\to N$ and $g:N\to P$ is the map $g\circ f$ with components $g_I\circ f_I$, $g_B\circ f_B$, $\rho_{g\circ f}(t,n)=\rho_g(f_I\circ t,n)\mathbin{\triangle}g_B[\rho_f(t,n)]$ and $\gamma_{g\circ f}(t,b)=\gamma_g(f_I\circ t,f_Bb)\mathbin{\triangle}\gamma_f(t,b)$, where $\triangle$ is symmetric difference.
--
--   **Theorem.** Let $f:M\to P$ and $g:N\to P$ be maps of arrays such that every point in the image of $\hat f$ lies in the image of $\hat g$. Then there is a map $k:M\to N$ with $g\circ k=f$:
--
--   $$
--   \hat f\bigl[\mathrm{Pts}(M)\bigr]\subseteq\hat g\bigl[\mathrm{Pts}(N)\bigr]\quad\Longrightarrow\quad\exists\,k:M\to N\ \ \text{with}\ \ g\circ k=f .
--   $$
--
--   This is the factorization step behind the coherence axiom of the abstract elementary class of arrays: if a structure presented by $M$ is a substructure of one presented by $N$, and both sit inside a third structure via maps $f$ and $g$, then the inclusion of the first into the second is realized by an array map.
--
--   **Formalization Note** The hypothesis is `∀ x, ∃ y, g.onPoint y = f.onPoint x`, and `g.comp k = f` is equality of maps, i.e. of all four components (index injection, base embedding, row shifts, column shifts). No set-theoretic hypothesis is involved.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/ArrayIsomorphisms.lean#L74-L115

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

open OAI OAI.CHObstruction OAI.CHObstruction.Arrays
universe u v w
open Cardinal Ordinal Order
open Tuples
open scoped symmDiff
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_16
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_17
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_18
variable {M N P : Data.{u}}
variable (e : RawIso M N)

theorem OAI.CHObstruction.Arrays.Map.factor (f : Map M P) (g : Map N P)
    (h : ∀ x : M.Carrier, ∃ y, g.onPoint y = f.onPoint x) :
    ∃ k : Map M N, g.comp k = f := by sorry
