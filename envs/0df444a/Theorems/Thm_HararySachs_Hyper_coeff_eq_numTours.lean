-- Prove2me | Theorems.Thm_HararySachs_Hyper_coeff_eq_numTours
-- name    : HararySachs.Hyper.coeff_eq_numTours
-- status  : Proved
-- author  : @milia
-- created : 2026-11-12T03:35:15.171191+00:00
-- url     : https://prove2.me/theorems/961a721a-8948-4209-94ea-4bcc39c6fd92
-- title:
--   Lemma 4, counting part — $[A^0]\,\partial^D\operatorname{tr}(A^L)$ equals the number of Euler tours of $D$
-- statement:
--   This is the counting identity at the heart of Lemma 4 of Clark and Cooper: extracting the constant term of a monomial differential operator applied to a matrix trace counts Euler tours.
--
--   Let $A=(A_{uv})_{u,v\in[n]}$ be a matrix of independent variables over $\mathbb Q$, and let $D$ be a directed multigraph on $[n]$ with $m(u,v)$ distinguishable arcs from $u$ to $v$ (loops allowed) and $L=\sum_{u,v}m(u,v)>0$ arcs in total. Put
--
--   $$
--   \partial^{D}=\prod_{u,v\in[n]}\frac{\partial^{\,m(u,v)}}{\partial A_{uv}^{\,m(u,v)}}.
--   $$
--
--   Then the constant term of $\partial^D\operatorname{tr}(A^L)$ equals the number of Euler tours of $D$:
--
--   $$
--   [A^0]\;\partial^{D}\operatorname{tr}\bigl(A^{L}\bigr)\;=\;\#\{\text{Euler tours of }D\}.
--   $$
--
--   An Euler tour is a closed trail that traverses every arc exactly once and has a distinguished first position. No Eulerian hypothesis is needed: when $D$ is not Eulerian, both sides vanish.
--
--   Together with Euler's criterion for the existence of a tour, this gives Lemma 4. Through the BEST theorem it also gives Corollary 6, the closed form of each summand of the differential trace $\operatorname{Tr}_d$.
--
--   **Formalization Note** The operator is the mission's `diffMonomial m`, and $\operatorname{tr}(A^L)$ is `trPow n L`. Euler tours are counted by `numTours m hL`: bijections from positions `Fin L` onto the labeled arcs `Arcs m` in which each arc's head is the next arc's tail, cyclically. The tour count $|E(D)|\,|\mathfrak E(D)|$ in the paper's Equation (3) is this number.
-- source:
--   Clark and Cooper, A Harary-Sachs theorem for hypergraphs, arXiv:1812.00468v2, p. 6, proof of Lemma 4 (f̂A^α = ∏ m(i,j)!, α describes ∏ m(i,j)! Euler tours, every Euler tour described by exactly one α) and Equation (3)

import Mathlib
import Definitions.Def_HararySachs_Hyper_Operators

namespace HararySachs.Hyper

theorem coeff_eq_numTours {n L : ℕ} (hL : 0 < L) (m : ArcMult n)
    (hm : (∑ u : Fin n, ∑ v : Fin n, m u v) = L) :
    MvPolynomial.coeff 0 (diffMonomial m (trPow n L)) = (numTours m hL : ℚ) := by sorry

end HararySachs.Hyper
