-- Prove2me | Theorems.Thm_MixedCloning_Optimal_Supplement_theorem_27
-- name    : MixedCloning.Optimal.Supplement.theorem_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:17:37.475614+00:00
-- url     : https://prove2.me/theorems/9f08b0ac-d5a4-41cd-b93c-af53bd8b15bf
-- title:
--   Theorem 27 (= Theorem 5) — the PTT transposer is sample-optimal
-- statement:
--   Fix integers $1\le r\le d$ and $k\ge1$. A channel $T$ from $(\mathbb C^d)^{\otimes n}$ to $(\mathbb C^d)^{\otimes k}$ **transposes rank-$r$ states to fidelity $1-\varepsilon$** if $F\bigl(T(\rho^{\otimes n}),(\rho^{\mathsf T})^{\otimes k}\bigr)\ge1-\varepsilon$ for every state $\rho$ of rank at most $r$, with the transpose in the computational basis. Let $n^{\mathsf T}_*(d,r,k,\varepsilon)$ be the least $n$ for which such a channel exists. Then:
--
--   1. **Lower bound.** If $d\ge2$ and $0<\varepsilon\le1/16$, every $n$ admitting such a channel satisfies, with $r'=\min(r,\lfloor d/2\rfloor)$,
--   $$n\ge\frac{kr'd}{8\varepsilon}\qquad\text{and}\qquad n\ge\frac{krd}{24\varepsilon}.$$
--   2. **PTT upper bound.** For every $n\ge1$, every random purification channel $R$ meeting the RPC specification and every state $\tau$, the PTT transposer is a channel with
--   $$F\bigl(\mathrm{PTT}(\rho^{\otimes n}),(\rho^{\mathsf T})^{\otimes k}\bigr)\ge1-\frac{krd}{n}$$
--   for every state of rank at most $r$; in particular it achieves fidelity $1-\varepsilon$ whenever $\varepsilon>0$ and $n\ge\lceil krd/\varepsilon\rceil$.
--   3. **Sample complexity.** If $d\ge2$ and $0<\varepsilon\le1/16$, the feasible set is nonempty and
--   $$\frac{krd}{24\varepsilon}\le n^{\mathsf T}_*(d,r,k,\varepsilon)\le\Bigl\lceil\frac{krd}{\varepsilon}\Bigr\rceil .$$
--
--   The paper writes $\Omega(krd/\varepsilon)$, $O(krd/\varepsilon)$ and $\Theta(krd/\varepsilon)$; its proofs yield the constants $1/8$ at rank $\min(r,\lfloor d/2\rfloor)$ (Proposition 26), hence $1/24$ for every $r\le d$, and $1$ for the upper bound (Proposition 25). Theorem 27 prints $\varepsilon\le1/16$; its restated form Theorem 5 (p. 8) writes a universal constant $\varepsilon_0$. This is the transposition counterpart of the mission's goal Theorem 1.
--
--   **Formalization Note** $F$ is the squared fidelity. The existence of an RPC channel for every $n$ is clause 2 of the mission's goal theorem and is not restated; together with clause 2 here it yields the upper bound in clause 3.
--
--   Differences from the source:
--   - encoding: $n=\Omega(krd/\varepsilon)$ → $n\ge kr'd/(8\varepsilon)$ with $r'=\min(r,\lfloor d/2\rfloor)$, and $n\ge krd/(24\varepsilon)$; reason: the proofs of Proposition 26 and Theorem 27 supply these constants
--   - encoding: $\varepsilon\le1/16$ → $0<\varepsilon\le1/16$; reason: the bound krd/ε is undefined at ε = 0
--   - encoding: $n=O(krd/\varepsilon)$ → every $n\ge1$ with fidelity $\ge1-krd/n$, and every $n\ge\lceil krd/\varepsilon\rceil$; reason: the proof of Proposition 25 supplies the explicit constant 1
--   - encoding: sample complexity $\Theta(krd/\varepsilon)$ → the infimum of the feasible input counts, asserted nonempty, between $krd/(24\varepsilon)$ and $\lceil krd/\varepsilon\rceil$; reason: an infimum over ℕ is 0 on the empty set, so nonemptiness is stated
--   - reading: the optimal pure-state transposer of [BGSQ26], given without a formula → the complementary channel of Werner's cloner, extended by a fixed state $\tau$ off the symmetric subspace; reason: p. 8 identifies the optimal pure-state transposer with the complement of Werner's cloner, and random purifications are symmetric
--   - generalization: the PTT transposer of Figure 8 → every channel satisfying the RPC specification and every complementary output state $\tau$; reason: they agree on tensor-power inputs of rank at most r, so the printed PTT is one instance
--   - reading: rank-$r$ states on $\mathbb C^d$ → $1\le r\le d$ and states of rank at most $r$; reason: a state on $\mathbb C^d$ has rank at most d, and rank at most r is the stronger reading stated in the theorem's hypothesis
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 29, Theorem 27 and its proof (restating Theorem 5, p. 8); Propositions 25 and 26, p. 27

import Definitions.Def_MixedCloning_Optimal_Supplement_Transposition

noncomputable section
open Matrix MixedCloning.Optimal
open scoped Matrix ComplexConjugate

namespace MixedCloning.Optimal.Supplement
attribute [local instance] Classical.propDecidable Classical.decEq

theorem theorem_27 (d r k : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d) (hk : 1 ≤ k) :
    (∀ (eps : ℝ), 0 < eps → eps ≤ 1/16 → 2 ≤ d →
      ∀ (n : ℕ) (T : Transposer d n k), Transposes d r n k eps T →
        (k : ℝ) * ((min r (d/2) : ℕ) : ℝ) * d / (8*eps) ≤ n ∧ (k : ℝ)*r*d/(24*eps) ≤ n) ∧
    (∀ (n : ℕ), 1 ≤ n →
      ∀ R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n), IsRPC d r n R →
      ∀ tau : Op (Word (Fin d × Fin r) k), IsState tau →
        Transposes d r n k ((k : ℝ)*r*d/n) (ptt d r n k R tau) ∧
        ∀ eps : ℝ, 0 < eps → Nat.ceil ((k : ℝ)*r*d/eps) ≤ n →
          Transposes d r n k eps (ptt d r n k R tau)) ∧
    (∀ eps : ℝ, 0 < eps → eps ≤ 1/16 → 2 ≤ d →
      (transposeFeasibleSamples d r k eps).Nonempty ∧
      (k : ℝ)*r*d/(24*eps) ≤ transposeSampleComplexity d r k eps ∧
      transposeSampleComplexity d r k eps ≤ Nat.ceil ((k : ℝ)*r*d/eps)) := by sorry

end MixedCloning.Optimal.Supplement
