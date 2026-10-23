-- Prove2me | Theorems.Thm_OSPMech_SqrtLB_observation_1
-- name    : OSPMech.SqrtLB.observation_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:40.112393+00:00
-- url     : https://prove2.me/theorems/c0e49a5a-e76e-461a-ad7b-5e50a51c747c
-- title:
--   Observation 1, p. 8 — OSP is equivalent to the OSP constraints (1) at every separating vertex
-- statement:
--   Let $\mathcal T$ be an implementation tree for $n$ agents with finite type domains $D_i$, let $\mathbf p$ be a payment function of the declared profile, and let $a(X)$ denote the cost of outcome $X$ for type $a$. A vertex $u$ is *$ab$-separating* for agent $i$ if $S(u) = i$ and some profiles $(a, \mathbf a_{-i})$ and $(b, \mathbf b_{-i})$ of $D$ are compatible with $u$ and diverge there.
--
--   The mechanism $(\mathcal T, \mathbf p)$ is OSP if and only if, for every agent $i$, every vertex $u$ labelled $i$, and all profiles $\mathbf a = (a, \mathbf a_{-i})$ and $\mathbf b = (b, \mathbf b_{-i})$ in $D$ that are compatible with $u$ and diverge at $u$,
--   $$p_i(\mathbf b) - p_i(\mathbf a) \le a(f(b, \mathbf b_{-i})) - a(f(a, \mathbf a_{-i})). \tag{1}$$
--
--   Inequality (1) is the *OSP constraint*: it rewrites the OSP condition for an agent of true type $a$ with utilities expanded. It is the linear system whose feasibility Theorem 3 characterizes.
-- source:
--   Ferraioli, Meier, Penna, Ventre, On the approximation guarantee of obviously strategyproof mechanisms, arXiv:1805.04190v2, p. 8, Observation 1 (eq. (1)); proof p. 24

import Mathlib
import Definitions.Def_OSPMech_SqrtLB_Model

namespace OSPMech.SqrtLB
theorem observation_1 {n : ℕ} {X : Type} (D : Fin n → Finset ℝ) (cost : Fin n → ℝ → X → ℝ)
    (t : ImplTree n X) (p : (Fin n → ℝ) → Fin n → ℝ) :
    IsOSP D cost t p ↔
      ∀ (pos : List ℕ) (i : Fin n) (a b : Fin n → ℝ), InDomain D a → InDomain D b →
        DivergeAt t pos i a b →
        p b i - p a i ≤ cost i (a i) (outcome t b) - cost i (a i) (outcome t a) := by sorry
end OSPMech.SqrtLB
