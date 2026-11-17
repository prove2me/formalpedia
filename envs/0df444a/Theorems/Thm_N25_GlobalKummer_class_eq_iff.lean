-- Prove2me | Theorems.Thm_N25_GlobalKummer_class_eq_iff
-- name    : N25.GlobalKummer.class_eq_iff
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:34.186238+00:00
-- url     : https://prove2.me/theorems/2020535a-a022-494e-872b-67d53d59fd3c
-- title:
--   Equality of division classes detects rational divisibility
-- statement:
--   Let $J$ be the level-$25$ Jacobian carrier, let $M=J(\mathbf Q)$ be its Galois-fixed subgroup, let $\gamma$ be the order-five diamond action, and set $\pi=2+4\gamma+\gamma^2$. Assume $1+\gamma+\gamma^2+\gamma^3+\gamma^4=0$ on $J$, and put $V=\ker\pi$. For $P,R\in M$, choose $Q,S\in J$ with $\pi Q=P$ and $\pi S=R$, and let $[\delta(P,Q)]$ and $[\delta(R,S)]$ be the classes in $H^1(\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q),V)$ of the cocycles $\sigma\mapsto\sigma Q-Q$ and $\sigma\mapsto\sigma S-S$. Then
--
--   $$[\delta(P,Q)]=[\delta(R,S)]\quad\Longleftrightarrow\quad P-R\in\pi(M).$$
--
--   This identifies equality of global division classes with divisibility by the selected endomorphism on rational points.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GlobalKummer

open N25
open N25.GlobalKummer

theorem N25.GlobalKummer.class_eq_iff (hPhi : PhiFiveZero) (P R : ↥M) (Q S : J)
    (hQ : piEnd Q = (P : J)) (hS : piEnd S = (R : J)) :
    groupCohomology.H1π (vRep hPhi) (divisionCocycle hPhi P Q hQ) =
      groupCohomology.H1π (vRep hPhi) (divisionCocycle hPhi R S hS) ↔
        P - R ∈ piM.range := by sorry
