-- Prove2me | Theorems.Thm_OAI_ParityWL_WeightedWitness_testMass_transfer
-- name    : OAI.ParityWL.WeightedWitness.testMass_transfer
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:37:52.641168+00:00
-- url     : https://prove2.me/theorems/1528a26f-1bbc-4a8e-95c8-dbdb84e872a0
-- title:
--   Transfer of tested witness mass across a separator
-- statement:
--   Let $T$ be a graph on a vertex set $A$, let $F$ be a graph on a finite vertex set $W$, and let $a\colon F\to T$ be a graph homomorphism; $a(x)$ is called the *type* of $x\in W$. Fix $b\colon A\to\mathbb{F}_2$. A *weighted witness* $w=(\lambda,\mu)$ for $(T,F,a,b)$ consists of vertex weights $\lambda\colon W\to\mathbb{F}_2$ and edge weights $\mu\colon W\times W\to\mathbb{F}_2$ such that $\mu(x,y)=\mu(y,x)$, $\mu(x,y)=0$ whenever $xy$ is not an edge of $F$, $\sum_{y\in W,\ a(y)=u}\mu(x,y)=\lambda(x)$ for every $x\in W$ and every neighbour $u$ of $a(x)$ in $T$, and $\sum_{x\in W}\lambda(x)\,b(a(x))=1$. For $Y\subseteq W$, a type $u\in A$ and a test function $p\colon W\to\mathbb{F}_2$, the *tested mass* of type $u$ on $Y$ is $m_Y(u;p)=\sum_{x\in Y,\ a(x)=u}\lambda(x)\,p(x)$.
--
--   **Theorem.** Let $w=(\lambda,\mu)$ be a weighted witness for $(T,F,a,b)$, let $u,v\in A$ be adjacent in $T$, let $Y,S\subseteq W$, and let $p,q\colon W\to\mathbb{F}_2$. Assume:
--
--   1. every edge $xy$ of $F$ with $x\in Y$ and $y\notin Y$ has $y\in S$;
--   2. no vertex of $S$ has type $v$;
--   3. $p(x)=0$ for every $x\in S$ of type $u$;
--   4. $p(x)=q(y)$ for every edge $xy$ of $F$ with $a(x)=u$ and $a(y)=v$.
--
--   Then
--   $$
--   \sum_{x\in Y,\ a(x)=u}\lambda(x)\,p(x)\;=\;\sum_{y\in Y,\ a(y)=v}\lambda(y)\,q(y),\qquad\text{that is,}\qquad m_Y(u;p)=m_Y(v;q).
--   $$
--
--   No further condition is placed on $S$ (it may meet $Y$), and every edge leaving $Y$ is accounted for by hypotheses 1 to 3 rather than being discarded. The identity moves the parity mass of a dual certificate across a separator from one template type to an adjacent one. With $Y=W$ and $S=\emptyset$ it yields global mismatch identities, and with label-dependent tests it is the engine of the argument extracting a solution of a choice system from a witness for the star-parity lift.
--
--   **Formalization Note** `WeightedWitness T F a b` has fields `vertex` ($\lambda$), `edge` ($\mu$), `symmetric`, `supported`, `coordinate` and `odd`; `Bit` is `ZMod 2`. The tested mass is `w.testMass Y u p`, and `Y S : Finset W`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/Masses.lean#L174-L226

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

theorem OAI.ParityWL.WeightedWitness.testMass_transfer (w : WeightedWitness T F a b)
    {u v : A} (huv : T.Adj u v) (Y S : Finset W) (p q : W → Bit)
    (hboundary : ∀ x ∈ Y, ∀ y, F.Adj x y → y ∉ Y → y ∈ S)
    (hv : ∀ x ∈ S, a x ≠ v)
    (hp : ∀ x ∈ S, a x = u → p x = 0)
    (hcompat : ∀ x y, F.Adj x y → a x = u → a y = v → p x = q y) :
    w.testMass Y u p = w.testMass Y v q := by sorry
