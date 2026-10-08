-- Prove2me | Theorems.Thm_FuzzyGames_Values_diag_axioms
-- name    : FuzzyGames.Values.diag_axioms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:01.145756+00:00
-- url     : https://prove2.me/theorems/2a005883-c73c-4f1f-9420-063c9c9aa0d8
-- title:
--   Theorem 8.1, proof — the diagonal maps (4) are Pareto optimal, symmetric and atomic
-- statement:
--   The maps $\psi_n:V^n\to\mathbb R^n$ given by the diagonal formula
--   $$(\psi_n v)_i=\int_0^1\frac{\partial v}{\partial\tau_i}(t\tau^N)\,dt$$
--   satisfy
--
--   1. Pareto optimality: $\sum_{i\in N}(\psi_n v)_i=v(\tau^N)$ for all $n\ge1$, $v\in V^n$;
--   2. the symmetry axiom: $\psi_n(\theta^*v)=\theta^*(\psi_n v)$ for every permutation $\theta$ of $N$, where $(\theta^*v)(\tau)=v(\tau_{\theta^{-1}(1)},\dots,\tau_{\theta^{-1}(n)})$ and $(\theta^*c)_i=c_{\theta(i)}$;
--   3. the atomicity axiom: for every partition $P$ of $N$ into $m$ nonempty types $A_1,\dots,A_m$ and $v\in V^n$, $\psi_m(P^*v)_j=\sum_{i\in A_j}(\psi_n v)_i$, where $(P^*v)(\sigma)=v(P\cdot\sigma)$.
--
--   Together with the linearity and continuity of the previous milestone, this says that the diagonal formula is a sequence of fuzzy values.
--
--   **Formalization Note** The paper derives symmetry and atomicity from (5) with $A=\theta^*$ and $A=P^*$; Pareto optimality is the implicit part of "it is clear". The games $\theta^*v$ and $P^*v$ are passed as elements of $V^n$, $V^m$ with their defining identities; a partition into nonempty types is a surjection `Fin n → Fin m`.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §8, proof of Theorem 8.1, p. 10 ("The symmetry and atomicity axioms follow by taking A = θ* and A = P*")

import Mathlib
import Definitions.Def_FuzzyGames_Values_Basic

namespace FuzzyGames.Values

/-- §8, proof of Theorem 8.1 (p. 10): the maps `ψ_n v = ∫_0^1 Dv(tτ^N) dt` of (4) satisfy
the Pareto optimality, symmetry and atomicity axioms. -/
theorem diag_axioms :
    IsParetoOptimal (fun n (v : Vn n) => diagValue v.1) ∧
      IsSymmetric (fun n (v : Vn n) => diagValue v.1) ∧
      IsAtomic (fun n (v : Vn n) => diagValue v.1) := by sorry

end FuzzyGames.Values
