-- Prove2me | Theorems.Thm_HararySachs_Hyper_lemma_4
-- name    : HararySachs.Hyper.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:40:26.016172+00:00
-- url     : https://prove2.me/theorems/63616dbc-a2f6-4ec0-a2fd-bed7d041f844
-- title:
--   Lemma 4 — differential trace and Euler tours
-- statement:
--   Let $D$ be a directed multigraph with $L>0$ arcs, counted with multiplicity, and let $\partial^D$ differentiate once for each arc $u\to v$ with respect to $A_{uv}$. Then
--
--   $$[A^0]\partial^D\operatorname{tr}(A^L)\ne0\quad\Longleftrightarrow\quad D\text{ is Eulerian}.$$
--
--   When $D$ is Eulerian, this constant equals the number of Euler tours with distinguishable parallel arcs and a specified first position, namely $L$ times the number of Euler circuits. This is the operator-to-digraph bridge for the trace calculation.
--
--   **Formalization Note** The statement allows every monomial differential operator of total degree $L$; the paper applies it to addends of the trace operator. Tours replace the equivalent product $|E(D)|\,|\mathfrak E(D)|$.
-- source:
--   Clark and Cooper, A Harary-Sachs theorem for hypergraphs, arXiv:1812.00468v2, p. 6, Lemma 4 and Equation (3)

import Mathlib
import Definitions.Def_HararySachs_Hyper_Operators

namespace HararySachs.Hyper

theorem lemma_4 {n L : ℕ} (hL : 0 < L) (m : ArcMult n)
    (hm : (∑ u : Fin n, ∑ v : Fin n, m u v) = L) :
    (MvPolynomial.coeff 0 (diffMonomial m (trPow n L)) ≠ 0 ↔ IsEulerian m) ∧
      (IsEulerian m →
        MvPolynomial.coeff 0 (diffMonomial m (trPow n L)) =
          (numTours m hL : ℚ)) := by sorry

end HararySachs.Hyper
