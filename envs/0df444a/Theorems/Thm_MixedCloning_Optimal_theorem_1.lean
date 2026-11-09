-- Prove2me | Theorems.Thm_MixedCloning_Optimal_theorem_1
-- name    : MixedCloning.Optimal.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:05:36.695246+00:00
-- url     : https://prove2.me/theorems/b149a65e-d197-4df1-829e-53e11833af9b
-- title:
--   Theorem 1 — sample-optimal mixed-state cloning
-- statement:
--   Fix integers $1\le r\le d$ and $k\ge1$. Put $r'=\min(r,\lfloor d/2\rfloor)$.
--
--   1. If $d\ge2$ and $0<\varepsilon\le1/16$, any channel $C$ cloning every state of rank at most $r$ from $n$ to $n+k$ copies with squared fidelity at least $1-\varepsilon$ must satisfy
--
--   $$n\ge\frac{kr'd}{8\varepsilon}\quad\text{and}\quad n\ge\frac{krd}{24\varepsilon}.$$
--
--   2. For every $n\ge0$, there exists an RPC with the action specified in Section 2.3.
--
--   3. For every $n\ge1$, every RPC $R$ and every complementary output state $\tau$, the completed PCT map is a channel and satisfies, for every state $\rho$ of rank at most $r$,
--
--   $$F(C_{\mathrm{PCT}}(\rho^{\otimes n}),\rho^{\otimes(n+k)})\ge1-\frac{krd}{n}.$$
--
--   For every $\varepsilon>0$, all such $n\ge\lceil krd/\varepsilon\rceil$ attain fidelity at least $1-\varepsilon$.
--
--   4. For $d\ge2$ and $0<\varepsilon\le1/16$, the set of feasible input-copy counts is nonempty, and its least element obeys
--
--   $$\frac{krd}{24\varepsilon}\le n_*(d,r,k,\varepsilon)\le\left\lceil\frac{krd}{\varepsilon}\right\rceil.$$
--
--   The paper writes $\Omega(krd/\varepsilon)$ and $O(krd/\varepsilon)$; its proofs yield $1/8$ at rank $r'$, $1/24$ uniformly for all admissible ranks, and upper constant $1$. This establishes the stated $\Theta(krd/\varepsilon)$ sample complexity, with the PCT construction attaining the upper rate.
--
--   Differences from the source:
--   - reading: rank-r states and rank at most r → 1 ≤ r ≤ d; reason: these are exactly the possible nonzero ranks in dimension d; allowing r>d literally would make the linear-in-r lower bound false
--   - encoding: rank min(r,d/2) → rank min(r,⌊d/2⌋); reason: projector rank is an integer; this rank is at least r/3 for d≥2
--   - encoding: O(krd/ε) and Ω(krd/ε) → upper constant 1, lower constants 1/8 and 1/24, and ε₀ = 1/16; reason: Proposition 10 and Lemma 17 give these constants; the proof of Theorem 18 gives rank reduction
--   - encoding: Werner map on the symmetric subspace → Werner map extended by a fixed output state on the orthogonal complement; reason: the extension is a total channel and agrees with the printed map on random purifications
--   - generalization: the PCT channel specified in Figures 1 and 7 → every channel satisfying the RPC specification and every complementary output state; reason: their action agrees on every tensor-power input, so the printed PCT guarantee follows
--   - encoding: Θ sample complexity → nonempty feasible set and bounds on its natural-number infimum; reason: nonemptiness excludes the default value of the infimum of the empty set
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 4, Theorem 1; Theorem 18 on p. 21; Section 2.3; Proposition 10; Lemma 17

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem theorem_1 (d r k : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d) (hk : 1 ≤ k) :
    (∀ (eps : ℝ), 0 < eps → eps ≤ 1/16 → 2 ≤ d →
      ∀ (n : ℕ) (C : Cloner d n (n+k)), Clones d r n k eps C →
        (k : ℝ) * ((min r (d/2) : ℕ) : ℝ) * d / (8*eps) ≤ n ∧ (k : ℝ)*r*d/(24*eps) ≤ n) ∧
    (∀ n : ℕ, ∃ R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n),
      IsRPC d r n R) ∧
    (∀ (n : ℕ), 1 ≤ n →
      ∀ R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n), IsRPC d r n R →
      ∀ tau : Op (Word (Fin d × Fin r) (n+k)), IsState tau →
        Clones d r n k ((k : ℝ)*r*d/n) (pct d r n k R tau) ∧
        ∀ eps : ℝ, 0 < eps → Nat.ceil ((k : ℝ)*r*d/eps) ≤ n →
          Clones d r n k eps (pct d r n k R tau)) ∧
    (∀ eps : ℝ, 0 < eps → eps ≤ 1/16 → 2 ≤ d →
      (feasibleSamples d r k eps).Nonempty ∧
      (k : ℝ)*r*d/(24*eps) ≤ sampleComplexity d r k eps ∧
      sampleComplexity d r k eps ≤ Nat.ceil ((k : ℝ)*r*d/eps)) := by sorry

end MixedCloning.Optimal
