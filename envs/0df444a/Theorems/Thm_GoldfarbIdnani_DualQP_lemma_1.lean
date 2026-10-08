-- Prove2me | Theorems.Thm_GoldfarbIdnani_DualQP_lemma_1
-- name    : GoldfarbIdnani.DualQP.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:15:06.898897+00:00
-- url     : https://prove2.me/theorems/2db9d282-2a25-44a3-9f56-a5e58b0f38c8
-- title:
--   Lemma 1 — moving from a V-triple along $z = Hn^+$: (3.7)–(3.11)
-- statement:
--   Let $G$ be symmetric positive definite and let $(x, A, p)$ be a V-triple for the quadratic program (1.1) (Definition 1: $p \notin A$, the normals of $A^+ = A \cup \{p\}$ are linearly independent, $s_p(x) < 0$, $s_i(x) = 0$ for $i \in A$, $H^+g(x) = 0$ and $u^+(x) = (N^+)^*g(x) \ge 0$). Let $n^+ = n_p$, let $H$ and $N^*$ be the operators (2.1)–(2.2) for $A$, and for $t \in \mathbb R$ consider
--
--   $$
--   \bar x = x + tz \quad (3.5), \qquad z = Hn^+ \quad (3.6).
--   $$
--
--   Then
--
--   1. $H^+g(\bar x) = 0$; (3.7)
--   2. $s_i(\bar x) = 0$ for all $i \in A$; (3.8)
--   3. $u^+(\bar x) \equiv (N^+)^*g(\bar x) = u^+(x) + t\begin{pmatrix}-r\\ 1\end{pmatrix}$, where $r = N^*n^+$; (3.9)–(3.10)
--   4. $s_p(\bar x) = s_p(x) + t\,z^{\mathsf T}n^+$. (3.11)
--
--   The lemma describes the line search of Step 2: along $z$ the point stays optimal on the manifold of $A^+$ except for the constraint $p$, and the multipliers move linearly in $t$.
--
--   **Formalization Note.** Multiplier vectors are indexed by constraint indices; the stacked vector $(-r; 1)$ of (3.9) is the vector with entry $1$ at $p$ and $-r_i$ at $i \in A$ (when $A = \emptyset$, $r$ is empty and $(-r;1) = (1)$). $t$ ranges over all reals, as printed.
-- source:
--   Goldfarb and Idnani, A numerically stable dual method for solving strictly convex quadratic programs, Math. Programming 27 (1983), p. 8, Lemma 1, Eqs. (3.5)–(3.11)

import Mathlib
import Definitions.Def_GoldfarbIdnani_DualQP_QP

namespace GoldfarbIdnani.DualQP

open Matrix

theorem lemma_1 {n m : ℕ} (a : Fin n → ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (A : Finset (Fin m)) (p : Fin m) (t : ℝ)
    (hG : G.PosDef) (hV : IsVTriple a G C b x A p) :
    let z := Hmat G C A *ᵥ normal C p
    let r := multVec G C A (normal C p)
    let xbar := x + t • z
    Hmat G C (insert p A) *ᵥ grad a G xbar = 0 ∧
    (∀ i ∈ A, slack C b xbar i = 0) ∧
    multVec G C (insert p A) (grad a G xbar) =
      dualStep (multVec G C (insert p A) (grad a G x)) r p t ∧
    slack C b xbar p = slack C b x p + t * (z ⬝ᵥ normal C p) := by sorry

end GoldfarbIdnani.DualQP
