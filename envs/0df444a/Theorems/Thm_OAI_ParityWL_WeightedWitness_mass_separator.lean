-- Prove2me | Theorems.Thm_OAI_ParityWL_WeightedWitness_mass_separator
-- name    : OAI.ParityWL.WeightedWitness.mass_separator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:37:06.127245+00:00
-- url     : https://prove2.me/theorems/84023b1c-e667-42bd-9d95-133588dbf931
-- title:
--   Two adjacent types absent from a separator carry equal witness mass on the separated set
-- statement:
--   Let $T$ be a simple graph on a set $A$, let $F$ be a simple graph on a finite set $W$, let $a:F\to T$ be a graph homomorphism (so $a(x)$ is the type of $x\in W$), and let $b:A\to\mathbb{F}_2$, where $\mathbb{F}_2=\mathbb{Z}/2\mathbb{Z}$. Let $(\omega,\varepsilon)$ be a weighted witness for $a$ and $b$: $\omega:W\to\mathbb{F}_2$ and $\varepsilon:W\times W\to\mathbb{F}_2$, with $\varepsilon$ symmetric and zero on non-edges of $F$, $\sum_{y\in W,\ a(y)=c}\varepsilon(x,y)=\omega(x)$ for every $x\in W$ and every neighbour $c$ of $a(x)$ in $T$, and $\sum_{x\in W}\omega(x)\,b(a(x))=1$. For $Y\subseteq W$ and $c\in A$, the mass of the type $c$ on $Y$ is
--   $$
--   \mu_Y(c)=\sum_{x\in Y,\ a(x)=c}\omega(x)\in\mathbb{F}_2 .
--   $$
--
--   Let $u,v\in A$ be adjacent in $T$, and let $Y,S\subseteq W$ be such that every edge of $F$ leaving $Y$ ends in $S$ (if $x\in Y$, $y\notin Y$ and $xy\in E(F)$, then $y\in S$), and no vertex of $S$ has type $u$ or type $v$. Then
--   $$
--   \mu_Y(u)=\mu_Y(v).
--   $$
--
--   In words, two adjacent template types that do not occur on a separator $S$ of the vertex set $Y$ carry the same witness mass on $Y$. Applied to the regions cut off by the bags of a tree decomposition of $F$, this local conservation law propagates information about masses through the decomposition in the parity reduction.
--
--   **Formalization Note** The witness is `w : WeightedWitness T F a b` and $\mu_Y(c)$ is `w.mass Y c`, a sum in `Bit = ZMod 2`; $Y$ and $S$ are `Finset`s of $W$, and $S$ is not required to be disjoint from $Y$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/Masses.lean#L60-L85

import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses

open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical
variable {A W : Type} [Fintype W]
variable {T : SimpleGraph A} {F : SimpleGraph W} {a : F →g T} {b : A → Bit}

theorem OAI.ParityWL.WeightedWitness.mass_separator (w : WeightedWitness T F a b)
    {u v : A} (huv : T.Adj u v) (Y S : Finset W)
    (hboundary : ∀ x ∈ Y, ∀ y, F.Adj x y → y ∉ Y → y ∈ S)
    (hu : ∀ x ∈ S, a x ≠ u) (hv : ∀ x ∈ S, a x ≠ v) :
    w.mass Y u = w.mass Y v := by sorry
