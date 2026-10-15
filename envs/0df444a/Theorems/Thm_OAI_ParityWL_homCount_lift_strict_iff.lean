-- Prove2me | Theorems.Thm_OAI_ParityWL_homCount_lift_strict_iff
-- name    : OAI.ParityWL.homCount_lift_strict_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:33:12.12246+00:00
-- url     : https://prove2.me/theorems/0a8c2be6-6f7c-417d-9e42-c9172897c0ae
-- title:
--   A parity lift receives strictly fewer homomorphisms than the zero lift iff some projected $\mathbb{F}_2$-system is inconsistent
-- statement:
--   Let $T$ be a simple graph on a finite vertex set $A$ (the template), let $G$ and $F$ be simple graphs on finite vertex sets $V$ and $W$, and let $\tau:G\to T$ be a graph homomorphism. Write $\mathbb{F}_2=\mathbb{Z}/2\mathbb{Z}$ and $N_T(c)$ for the neighbourhood of $c\in A$ in $T$. For a parity function $b:A\to\mathbb{F}_2$, the parity lift $\widetilde G_b$ is the simple graph whose vertices are the pairs $(u,z)$ with $u\in V$ and $z:N_T(\tau(u))\to\mathbb{F}_2$ satisfying $\sum_{c\in N_T(\tau(u))}z(c)=b(\tau(u))$, two vertices $(u,z)$ and $(u',z')$ being adjacent iff $uu'\in E(G)$ and $z(\tau(u'))=z'(\tau(u))$. Let $\widetilde G_0$ be the lift for $b\equiv0$, and let $\hom(F,K)$ be the number of graph homomorphisms $F\to K$.
--
--   For a homomorphism $\varphi:F\to G$, the projected lift system $\mathcal S_\varphi(b)$ has one unknown $z_x(c)\in\mathbb{F}_2$ for every $x\in W$ and every $c\in N_T(\tau\varphi(x))$, and the equations
--   $$
--   \sum_{c\in N_T(\tau\varphi(x))}z_x(c)=b(\tau\varphi(x))\quad(x\in W),\qquad z_x(\tau\varphi(y))=z_y(\tau\varphi(x))\quad(xy\in E(F)).
--   $$
--   Then
--   $$
--   \hom(F,\widetilde G_b)<\hom(F,\widetilde G_0)\iff\text{there is a homomorphism }\varphi:F\to G\text{ such that }\mathcal S_\varphi(b)\text{ has no solution.}
--   $$
--
--   Since $\hom(F,\widetilde G_b)\le\hom(F,\widetilde G_0)$ holds for every $b$, the theorem says exactly when a parity lift has strictly fewer homomorphisms from $F$ than the zero lift: the deficit is caused by a single projected system that is inconsistent. In the parity reduction this turns a homomorphism-count gap between the zero lift and the star lift into an unsolvable linear system over $\mathbb{F}_2$, to which linear duality can then be applied.
--
--   **Formalization Note** $\hom(F,K)$ is `homCount F K`, the cardinality of the type `F →g K`; the lift is `liftGraph T G τ b`, and $\mathcal S_\varphi(b)$ is the type `Solutions T G F τ φ b` of assignments satisfying `LiftEquations`. The homomorphism $\varphi$ in the statement is bound by the existential quantifier.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/LiftCounts.lean#L161-L176

import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts

open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical
variable {A V W : Type} [Fintype A] [Fintype V] [Fintype W]
variable (T : SimpleGraph A) (G : SimpleGraph V) (F : SimpleGraph W)
variable (τ : G →g T) (φ : F →g G)

theorem OAI.ParityWL.homCount_lift_strict_iff (b : A → Bit) :
    homCount F (liftGraph T G τ b) < homCount F (liftGraph T G τ (fun _ => 0)) ↔
      ∃ φ : F →g G, ¬ Nonempty (Solutions T G F τ φ b) := by sorry
