-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_lemma_7_1
-- name    : HindsightGain.Uniform.Supplement.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:59:01.259181+00:00
-- url     : https://prove2.me/theorems/c1e81d0e-c45a-4abf-b2d0-7b7ec9828a15
-- title:
--   Lemma 7.1 — Sampling product-state energies with $O_r(d^r\varepsilon^{-2})$ particles
-- statement:
--   Fix $r\ge2$. There are constants $C_r,C_r'>0$ depending only on $r$ such that the following holds. Let $H=\sum_{|e|=r}h_e$ be a Hamiltonian on $n\ge1$ particles of local dimension $d\ge1$, with exactly $r$-body Hermitian terms of operator norm at most one (at most one per subset; zero terms allowed). For every integer $1\le q\le n$ and a uniformly random $q$-element set $S\subseteq[n]$, with probability at least $0.99$,
--   $$\Big|\Big(\frac nq\Big)^rP(H_S)-P(H)\Big|\le C_r\,d^{r/2}\frac{n^r}{\sqrt q}.\tag{39}$$
--   In particular, for every $\varepsilon\in(0,1)$, the sample size $q=\min\{n,\lceil C_r'd^r\varepsilon^{-2}\rceil\}$ gives $|(n/q)^rP(H_S)-P(H)|\le\varepsilon n^r$ with probability at least $0.99$.
--
--   This is the product-state step of the ground-state sampling theorem.
--
--   Differences from the source:
--   - encoding: Hermitian local terms h_e acting on the particles in e, with identities elsewhere, and E_0(H_U), P(H_U) on the particles of U → matrices indexed by labelings of e, embedded into the n-particle space with identities; E_0 as the infimum of ⟨v,Hv⟩ over unit vectors of the whole space; product states chosen for all particles; reason: the minimum eigenvalue of H_U ⊗ I equals that of H_U, it is 0 for U = ∅, and particles outside U do not affect P(H_U)
--   - encoding: ‖h_e‖_op ≤ 1 → ‖h_e v‖ ≤ ‖v‖ for every vector v; reason: definition of the operator norm bound
--   - encoding: a uniformly random q-element subset S → the proportion of q-element subsets satisfying the event; reason: this is the uniform law on q-element subsets
--   - encoding: O_r(d^r ε^{−2}) sampled particles suffice, taking the whole instance if this number exceeds n → q = min{n, ⌈C'_r d^r ε^{−2}⌉} with C'_r depending only on r; reason: O_r with an explicit constant; the ceiling makes the sample size an integer
--   - encoding: an integer 1 ≤ q ≤ n → the hypothesis 1 ≤ n; reason: the range of q is nonempty only for n ≥ 1
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Lemma 7.1, p.29 (eq. (39)); definitions (37), p.29

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_quantum

set_option autoImplicit false

namespace HindsightGain.Uniform.Supplement

/-- Lemma 7.1, p.29: exactly `r`-body Hermitian terms of operator norm at most one, local
dimension `d ≥ 1`; `C_r` and `C'_r` depend only on `r`. First clause: (39) for every integer
`1 ≤ q ≤ n` and a uniformly random `q`-subset `S`. Second clause: `q = min{n, ⌈C'_r d^r ε^{-2}⌉}`
sampled particles give additive error `εn^r` with probability at least `0.99`. -/
theorem lemma_7_1 (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∃ C' : ℝ, 0 < C' ∧
      ∀ (d n : ℕ) (h : (e : Finset (Fin n)) → Matrix (LocalConfig e d) (LocalConfig e d) ℂ),
        1 ≤ d → 1 ≤ n → (∀ e, (h e).IsHermitian) → (∀ e, OpNormLeOne (h e)) →
        (∀ e, e.card ≠ r → h e = 0) →
        (∀ q : ℕ, 1 ≤ q → q ≤ n →
          99 / 100 ≤ unifProb q (fun S : Finset (Fin n) =>
            |((n : ℝ) / q) ^ r * productEnergy h S - productEnergy h Finset.univ| ≤
              C * (d : ℝ) ^ ((r : ℝ) / 2) * (n : ℝ) ^ r / Real.sqrt q)) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 →
          99 / 100 ≤ unifProb (min n ⌈C' * (d : ℝ) ^ r * (ε⁻¹) ^ 2⌉₊) (fun S : Finset (Fin n) =>
            |((n : ℝ) / (min n ⌈C' * (d : ℝ) ^ r * (ε⁻¹) ^ 2⌉₊ : ℕ)) ^ r * productEnergy h S -
                productEnergy h Finset.univ| ≤ ε * (n : ℝ) ^ r)) := by sorry

end HindsightGain.Uniform.Supplement
