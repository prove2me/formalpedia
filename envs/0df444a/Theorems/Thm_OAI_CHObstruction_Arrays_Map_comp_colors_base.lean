-- Prove2me | Theorems.Thm_OAI_CHObstruction_Arrays_Map_comp_colors_base
-- name    : OAI.CHObstruction.Arrays.Map.comp_colors_base
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:01:16.912822+00:00
-- url     : https://prove2.me/theorems/3e819ed3-170e-4b79-bdea-5e0667ab8e03
-- title:
--   Twisted colors of a composite array map at base points of the intermediate array
-- statement:
--   Let $\mathcal C$ (the *palette*) be the set of binary sequences $a:\mathbb N\to\{0,1\}$ modulo the equivalence relation of differing in only finitely many places, and write $[a]\in\mathcal C$ for the class of $a$. For a set $I$, $\mathrm{Tup}(I)$ is the set of *tuples* in $I$, i.e. injective maps $t:\{0,\dots,n\}\to I$ with $n\in\mathbb N$ (of length $n+1$); for a strictly increasing $e:\{0,\dots,m\}\to\{0,\dots,n\}$ the tuple $t\circ e$ is a *subtuple* of $t$, and an injection $h:I\to I'$ sends $t$ to $h\circ t\in\mathrm{Tup}(I')$.
--
--   An *array* $M$ consists of a nonempty set $I_M$ of *indices*, a nonempty set $B_M$ of *base points* carrying a dense linear order without endpoints in which every closed interval is countable, and a *bit matrix* $\beta_M:\mathrm{Tup}(I_M)\times\mathbb N\times B_M\to\{0,1\}$. A *map* $f:M\to N$ of arrays consists of an injection $f_I:I_M\to I_N$, an order embedding $f_B:B_M\to B_N$, finite *row shifts* $\rho_f(t,n)\subseteq B_N$ and finite *column shifts* $\gamma_f(t,b)\subseteq\mathbb N$ ($t\in\mathrm{Tup}(I_M)$, $n\in\mathbb N$, $b\in B_M$) satisfying the bit identity
--   $$\beta_N(f_I\circ t,n,f_Bb)\oplus[f_Bb\in\rho_f(t,n)]\oplus[n\in\gamma_f(t,b)]=\beta_M(t,n,b),$$
--   where $\oplus$ is exclusive or and $[\,\cdot\,]\in\{0,1\}$ is the truth value of a statement. The composite of $f:M\to N$ and $g:N\to P$ is the map $g\circ f$ with components $g_I\circ f_I$, $g_B\circ f_B$, $\rho_{g\circ f}(t,n)=\rho_g(f_I\circ t,n)\mathbin{\triangle}g_B[\rho_f(t,n)]$ and $\gamma_{g\circ f}(t,b)=\gamma_g(f_I\circ t,f_Bb)\mathbin{\triangle}\gamma_f(t,b)$, where $\triangle$ is symmetric difference.
--
--   For a map $f:M\to N$, a tuple $t\in\mathrm{Tup}(I_M)$ and a base point $b\in B_N$ of the target, the *twisted color* is
--   $$\chi_f(t,b)=\bigl[\,n\mapsto\beta_N(f_I\circ t,n,b)\oplus[b\in\rho_f(t,n)]\,\bigr]\in\mathcal C .$$
--
--   **Theorem.** Let $f:M\to N$ and $g:N\to P$ be maps of arrays. For every tuple $t\in\mathrm{Tup}(I_M)$ and every base point $b\in B_N$,
--
--   $$
--   \chi_{g\circ f}(t,g_Bb)=\chi_f(t,b).
--   $$
--
--   Thus the twisted colors of a composite, at base points coming from the intermediate array, are those of the first map. This is the basic bookkeeping identity for strong maps, whose definition tests twisted colors at base points outside the range of a map; it is used to show that composites and first factors of strong maps, and the canonical maps into directed limits, satisfy the test conditions.
--
--   **Formalization Note** Arrays are `Data`, maps are `Map`, the composite is `Map.comp g f`, and $\chi_f$ is `Map.colors f`, with values in `Palette = ULift Color`; $\oplus$ is Boolean `xor`. No set-theoretic hypothesis is involved.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/ArrayEmbeddings.lean#L103-L120

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

theorem OAI.CHObstruction.Arrays.Map.comp_colors_base (g : Map N P) (f : Map M N) (t : Tuple M.I) (b : N.B) :
    (g.comp f).colors t (g.base b) = f.colors t b := by sorry
