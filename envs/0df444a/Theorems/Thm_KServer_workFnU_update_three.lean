-- Prove2me | Theorems.Thm_KServer_workFnU_update_three
-- name    : KServer.workFnU_update_three
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T15:47:40.252613+00:00
-- url     : https://prove2.me/theorems/04ed907d-86aa-4abb-9b17-ed7b2e2cf57a
-- title:
--   The update formula for three servers
-- statement:
--   Let $w$ be a work function whose **last request** is $r$ — that is, $w = w' \wedge r$ for the work function $w'$ before that request, so that $w$ is already saturated at $r$. Bein, Chrobak and Larmore record, as their equation (5), that the value of such a $w$ at an arbitrary three-point configuration is obtained by sending exactly one of its three servers to $r$:
--
--   $$w(s,x,y) \;=\; \min\bigl\{\, w(r,x,y) + rs,\;\; w(s,r,y) + rx,\;\; w(s,x,r) + ry \,\bigr\}.$$
--
--   ## Why this holds
--
--   The update operator has the closed form $w' \wedge r\,(X) = \min_{x \in X}\bigl(w'(X - x + r) + rx\bigr)$: an optimal offline schedule serving the new request $r$ and finishing at $X$ moves some server to $r$ and, by the triangle inequality along the matching, may be taken to move that same server on to its final position last. Because every configuration appearing on the right-hand side already contains $r$, the two work functions $w'$ and $w = w' \wedge r$ agree on it, and the formula can be written purely in terms of $w$ — which is the form displayed above, and the form in which it is used.
--
--   The three branches correspond to the three choices of which server travels to $r$, at a cost equal to the distance from that server's position to $r$.
--
--   ## Role
--
--   This is the workhorse of the three-server analysis. Every one of the twelve cases in the proof that the semi-lazy potential satisfies the update property begins by splitting each of the work-function values appearing in the potential according to which of these three branches realises the minimum, and the Manhattan-plane verification uses it in the same way. Having it as a single equation — rather than an inequality in each direction — is what makes those case analyses a matter of substitution and rearrangement.
--
--   **Formalization note.** Configurations are labelled maps `Fin 3 → M` in Mathlib's `![·,·,·]` notation; since `workFnU` is invariant under relabelling, each side depends only on the underlying multiset, and no distinctness of $r, s, x, y$ is assumed. The hypothesis that $r$ is the last request is expressed by writing the request sequence as `σ ++ [r]`.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Section 3, equation (5); the underlying closed form of the update operator is derived in Section 2 of the same paper.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_update_three (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (r s x y : M) :
    workFnU C₀ (σ ++ [r]) ![s, x, y]
      = min (workFnU C₀ (σ ++ [r]) ![r, x, y] + dist r s)
          (min (workFnU C₀ (σ ++ [r]) ![s, r, y] + dist r x)
               (workFnU C₀ (σ ++ [r]) ![s, x, r] + dist r y)) := by sorry

end KServer
