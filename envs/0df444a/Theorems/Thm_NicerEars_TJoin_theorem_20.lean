-- Prove2me | Theorems.Thm_NicerEars_TJoin_theorem_20
-- name    : NicerEars.TJoin.theorem_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:46.745693+00:00
-- url     : https://prove2.me/theorems/c9c4ca48-e464-4cfd-b074-7add40368da8
-- title:
--   Theorem 20 — L_µ(G,M) ≤ LP(G,T)
-- statement:
--   Let $G$ be a connected graph, $T\subseteq V(G)$ with $|T|$ even, and $M$ an eardrum in $G$ with $V_M\cap T=\emptyset$ and $\mathcal P_f\neq\emptyset$ for all $f\in M$. Then
--   $$L_\mu(G,M):=|V(G)|-1+|M|-\mu(G,M)\ \le\ \mathrm{LP}(G,T).$$
--   In particular, every connected-$T$-join of $G$ has at least $L_\mu(G,M)$ edges.
--
--   This is the lower bound against which the first construction (Theorem 24) is compared.
--
--   **Formalization Note.** $L_\mu(G,M)\le \mathrm{LP}(G,T)$ is stated as: every feasible point $x$ of $\mathrm{LP}(G,T)$ has $x(E(G))\ge L_\mu(G,M)$.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 16, Theorem 20

import Mathlib
import Definitions.Def_NicerEars_TJoin_Earmuff

namespace NicerEars.TJoin

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Theorem 20 (p. 16): `G` connected, `|T|` even, `M` an eardrum in `G` with `V_M ∩ T = ∅` and
`𝒫_f ≠ ∅` for all `f ∈ M`. Then `L_µ(G, M) = |V(G)| − 1 + |M| − µ(G, M) ≤ LP(G, T)` (every
LP(G, T)-feasible point has value at least `L_µ(G, M)`); in particular every connected-T-join of
`G` has at least `L_µ(G, M)` edges. -/
theorem theorem_20 (G : Graph V E) (hG : G.IsConnected) (T : Finset V) (hT : Even #T)
    (M : Finset (Finset V)) (hM : IsEardrum G M) (hMT : Disjoint (VM M) T)
    (hP : ∀ f ∈ M, (PathsThrough G f).Nonempty) :
    (∀ x : E → ℝ, G.LPTFeasible T x → (Lmu G M : ℝ) ≤ ∑ e, x e) ∧
    ∀ F : Finset (E × Fin 2), G.IsConnectedTJoin T F → Lmu G M ≤ (#F : ℤ) := by sorry

end NicerEars.TJoin
