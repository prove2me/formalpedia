-- Prove2me | Theorems.Thm_OAI_ParityWL_liftEquations_iff
-- name    : OAI.ParityWL.liftEquations_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:33:55.48473+00:00
-- url     : https://prove2.me/theorems/75aef74d-59ef-4942-914b-357b5bc7e8aa
-- title:
--   The parity-lift equations as a linear system $M_\varphi z=c_b$ over $\mathbb{F}_2$
-- statement:
--   Let $T$ be a simple graph on a finite set $A$, let $G$ and $F$ be simple graphs on sets $V$ and $W$, let $\tau:G\to T$ and $\varphi:F\to G$ be graph homomorphisms, and let $b:A\to\mathbb{F}_2$, where $\mathbb{F}_2=\mathbb{Z}/2\mathbb{Z}$. An assignment is a family $z=(z_x)_{x\in W}$ of functions $z_x:N_T(\tau\varphi(x))\to\mathbb{F}_2$, where $N_T(c)$ is the neighbourhood of $c$ in $T$; the assignments form an $\mathbb{F}_2$-vector space $\mathcal Z_\varphi$. The lift equations for $z$ are
--   $$
--   \sum_{c\in N_T(\tau\varphi(x))}z_x(c)=b(\tau\varphi(x))\quad\text{for all }x\in W,\qquad z_x(\tau\varphi(y))=z_y(\tau\varphi(x))\quad\text{for all }xy\in E(F).
--   $$
--
--   Index equations by the set $R=W\sqcup\vec E(F)$, where $\vec E(F)$ is the set of darts of $F$ (ordered pairs $(x,y)$ with $xy\in E(F)$). The $\mathbb{F}_2$-linear constraint map $M_\varphi:\mathcal Z_\varphi\to\mathbb{F}_2^{R}$ and the right-hand side $c_b\in\mathbb{F}_2^{R}$ are
--   $$
--   (M_\varphi z)(x)=\sum_{c\in N_T(\tau\varphi(x))}z_x(c),\qquad(M_\varphi z)(x,y)=z_x(\tau\varphi(y))+z_y(\tau\varphi(x)),\qquad c_b(x)=b(\tau\varphi(x)),\qquad c_b(x,y)=0 .
--   $$
--   Then for every assignment $z$,
--   $$
--   z\text{ satisfies the lift equations}\iff M_\varphi z=c_b .
--   $$
--
--   The theorem recasts the projected parity-lift system as a single linear equation $M_\varphi z=c_b$ over $\mathbb{F}_2$. In this form the linear alternative over $\mathbb{F}_2$ applies, and an inconsistent system produces a dual certificate.
--
--   **Formalization Note** The assignment space is `Variables T G F τ φ`, the lift equations are `LiftEquations T G F τ φ b z`, the row set is `EquationRow F = W ⊕ F.Dart`, and $M_\varphi$ and $c_b$ are `constraintMap T G F τ φ` and `constraintRHS T G F τ φ b`. No finiteness of $V$ or $W$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/LiftCounts.lean#L204-L223

import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts

open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical
variable {A V W : Type} [Fintype A] [Fintype V] [Fintype W]
variable (T : SimpleGraph A) (G : SimpleGraph V) (F : SimpleGraph W)
variable (τ : G →g T) (φ : F →g G)

omit [Fintype V] [Fintype W] in
theorem OAI.ParityWL.liftEquations_iff (b : A → Bit) (z : Variables T G F τ φ) :
    LiftEquations T G F τ φ b z ↔
      constraintMap T G F τ φ z = constraintRHS T G F τ φ b := by sorry
