-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_theorem_6
-- name    : HindsightGain.Uniform.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:59:32.763414+00:00
-- url     : https://prove2.me/theorems/4c97a92a-2682-4492-98fb-619df3aaebf3
-- title:
--   Theorem 6 — Sampling quantum ground-state energies with $O(\varepsilon^{-3})$ particles
-- statement:
--   Fix an integer $r\ge2$ and a single-particle space $\mathbb C^d$, $d\ge1$. There is a constant $C>0$ (depending on $r$ and $d$) such that the following holds. Let $H=\sum_{1\le|e|\le r}h_e$ be an $r$-local Hamiltonian on $n\ge1$ particles, with at most one Hermitian term $h_e$ of operator norm at most one on each nonempty subset of at most $r$ particles. Let $\varepsilon\in(0,1)$, put $q=\min\{n,\lceil C\varepsilon^{-3}\rceil\}$, and choose $S\subseteq[n]$ uniformly among its $q$-element subsets. Then, with probability at least $0.99$,
--   $$\Big|\Big(\frac nq\Big)^rE_0(H_S)-E_0(H)\Big|\le\varepsilon n^r ,$$
--   where $E_0$ is the minimum eigenvalue (entangled states allowed) and $H_S$ keeps the terms supported in $S$.
--
--   No commutativity, positivity, diagonal form or interaction-graph regularity is assumed.
--
--   Differences from the source:
--   - encoding: Hermitian local terms h_e acting on the particles in e, with identities elsewhere, and E_0(H_U), P(H_U) on the particles of U → matrices indexed by labelings of e, embedded into the n-particle space with identities; E_0 as the infimum of ⟨v,Hv⟩ over unit vectors of the whole space; product states chosen for all particles; reason: the minimum eigenvalue of H_U ⊗ I equals that of H_U, it is 0 for U = ∅, and particles outside U do not affect P(H_U)
--   - encoding: ‖h_e‖_op ≤ 1 → ‖h_e v‖ ≤ ‖v‖ for every vector v; reason: definition of the operator norm bound
--   - encoding: a uniformly random q-element subset S → the proportion of q-element subsets satisfying the event; reason: this is the uniform law on q-element subsets
--   - encoding: a fixed single-particle state space → ℂ^d with d ≥ 1 fixed before C; reason: finite-dimensional state spaces are ℂ^d
--   - encoding: n particles → the hypothesis 1 ≤ n; reason: the sample size q ≥ 1 needs n ≥ 1
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Theorem 6, p.31 (also stated p.8)

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_quantum

set_option autoImplicit false

namespace HindsightGain.Uniform.Supplement

/-- Theorem 6, p.31 (also p.8): `r ≥ 2` and local dimension `d ≥ 1` fixed before `C`; at most one
Hermitian term of operator norm at most one on each subset of `1` to `r` particles (no
commutativity, positivity or product-state restriction); `q = min{n, ⌈Cε^{-3}⌉}`, `S` a uniformly
random `q`-subset, and `E_0` the minimum eigenvalue (entangled states allowed). -/
theorem theorem_6 (r d : ℕ) (hr : 2 ≤ r) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (h : (e : Finset (Fin n)) → Matrix (LocalConfig e d) (LocalConfig e d) ℂ),
        1 ≤ n → (∀ e, (h e).IsHermitian) → (∀ e, OpNormLeOne (h e)) →
        (∀ e, (e.card = 0 ∨ r < e.card) → h e = 0) →
        ∀ ε : ℝ, 0 < ε → ε < 1 →
          99 / 100 ≤ unifProb (min n ⌈C * (ε⁻¹) ^ 3⌉₊) (fun S : Finset (Fin n) =>
            |((n : ℝ) / (min n ⌈C * (ε⁻¹) ^ 3⌉₊ : ℕ)) ^ r * groundEnergy (restrictHam h S) -
                groundEnergy (restrictHam h Finset.univ)| ≤ ε * (n : ℝ) ^ r) := by sorry

end HindsightGain.Uniform.Supplement
