-- Prove2me | Theorems.Thm_MixedManna_algorithm1_terminates_at_competitiveEquilibrium
-- name    : MixedManna.algorithm1_terminates_at_competitiveEquilibrium
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:09.669995+00:00
-- url     : https://prove2.me/theorems/e77afe40-3af2-45a7-a14e-e31de66dc757
-- title:
--   Theorem 14 — Algorithm 1 terminates at a competitive equilibrium in finite time
-- statement:
--   Consider an instance satisfying the standing assumptions of §§2 and 4 (unit supplies, SPLC slopes with strictly negative slopes on bads, desire for every good above 1, Conditions 1 and 2) and fix $P>0$. There is $R_0$ such that for every $R\ge R_0$, every admissible $\delta$ ($1<\delta_j<1+1/m$ on goods) and every last-segment length $1+\varepsilon$, $\varepsilon>0$, the following holds provided every vertex of $\mathcal P$ with $z>0$, $p<P$, $r<R$ is nondegenerate:
--
--   1. (termination) Algorithm 1, started from the primary ray $S_0$, reaches after finitely many pivots a vertex with $z=0$;
--   2. (correctness) every path of Algorithm 1 from $S_0$ that reaches a vertex $w$ with $z=0$ ends with $p_j<P$ for all $j\in M$ and $r_i<R$ for all $i\in N$, and the decoded prices and allocation
--   $$
--   p^*_j=\pm(P-p_j),\qquad x^*_{ij}=\frac{\sum_kf_{ijk}}{P-p_j}
--   $$
--   form a competitive equilibrium of the instance.
--
--   This is the paper's main result: a complementary pivot algorithm computes a competitive equilibrium of a mixed manna under SPLC utilities. Existence of equilibria, PPAD membership and rationality (Theorems 21–23) follow from it.
--
--   Differences from the source:
--   - reading: bads: 0 ≥ U_ijk > U_ijk′ (p.14), which allows U_ij1 = 0 → every slope on a bad is strictly negative, D_ijk = |U_ijk| > 0 (StandingAssumptions.bad_slope_neg); reason: the paper's working assumption in its proofs (p.24: 0 < D_ij1 < ⋯; p.43: D_ijk = |U_ijk| > 0 for all (i, j, k)); with D_ij1 = 0, (14d) fails at S₀ and Algorithm 1 cannot start; indifference_j < 1 for bads then holds automatically and is not stated
--   - encoding: a set of agents N and a set of items M → finite types with N nonempty; segments indexed from 0; reason: a market with no agents has no items (unit supply); Lean convention for indices; same instances otherwise
--   - reading: the input parameters U, W, and L have no polynomial relationship among them → every vertex of 𝒫 with z > 0, p < P, r < R is nondegenerate (NondegenerateInRegion); reason: the printed condition is undefined and, read as algebraic independence of the entries, never holds (Σ_i W_ij = 1), which would make the theorem vacuous; the proof uses it only through Theorem 11 (pp.22, 28)
--   - generalization: no polynomial relationship (through Theorem 11) → the conclusion of Theorem 11 as the hypothesis; reason: under any reading of the condition for which Theorem 11 holds the hypothesis is satisfied, so the statement specializes to the paper's
--   - reading: for sufficiently large R (p.22; Theorem 20's proof, p.27) → ∃ R₀, ∀ R ≥ R₀ (R₀ depending on the instance and P only); reason: the explicit list on p.22 cannot hold for zero-slope good segments (P − U_ijk R < 0 fails when U_ijk = 0), so the threshold is existential
--   - generalization: δ_j = 1 + ϵ_j with ϵ_j a uniform random number from (0, 1/m) (p.21) → every δ with 1 < δ_j < 1 + 1/m on goods (IsAdmissibleDelta); reason: every draw lies in the interval, so the statement specializes to the paper's
--   - generalization: last segment of length 1 + ϵ for some small ϵ > 0 in the LCP (p.14, p.23) → every ε > 0 (lcpLength); reason: the proofs use only that the length exceeds 1; specializes to small ε
--   - encoding: Algorithm 1 terminates at a competitive equilibrium in finite time → (A) some IsLemkePath w T with z(w T) = 0; (B) every IsLemkePath w T with z(w T) = 0 has p < P, r < R and its decoding is a competitive equilibrium; reason: under the nondegeneracy hypothesis the paths from S₀ are the vertex sequences of Algorithm 1 (p.6, p.22); the loop stops when z = 0
--   - encoding: the equilibrium read off the final vertex: x*_ij = Σ_k f_ijk / p*_j (p.45) → x*_ij = Σ_k f_ijk / (P − p_j) (decodeAlloc); reason: for a bad p*_j < 0 ≤ f_ijk and −f_ijk is the amount earned (p.17)
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, Theorem 14, p.22 (PDF p.24); proof p.28

import Mathlib
import Definitions.Def_MixedManna_StandingAssumptions
import Definitions.Def_MixedManna_IsAdmissibleDelta
import Definitions.Def_MixedManna_IsNondegenerateVertex
import Definitions.Def_MixedManna_IsLemkePath
import Definitions.Def_MixedManna_IsCompetitiveEquilibrium
import Definitions.Def_MixedManna_decodePrice

namespace MixedManna

open Classical

/-- **Theorem 14** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive Allocation of a Mixed Manna*, arXiv:2008.02753v1, p.22): "If the input parameters U, W, and L have no polynomial
relationship among them, then Algorithm 1 terminates at a competitive equilibrium in finite time."

Stated: for every instance satisfying the standing assumptions of §§2, 4 and every `P > 0` there is
`R₀` such that for every `R ≥ R₀`, every admissible `δ` (`1 < δ_j < 1 + 1/m`) and every
last-segment length `1 + ε`, `ε > 0`: if every vertex of `𝒫` with `z > 0`, `p < P`, `r < R` is
nondegenerate, then
(A) some path of Algorithm 1 from the primary ray reaches a vertex with `z = 0`, and
(B) every such path that reaches `z = 0` ends at a point with `p_j < P` for all `j`, `r_i < R`
for all `i`, whose decoding `p*_j = ±(P − p_j)`, `x*_ij = Σ_k f_ijk / (P − p_j)` is a competitive
equilibrium.

**Formalization Note** The hypothesis "no polynomial relationship among U, W, L" is replaced by the
property the proof takes from it, the conclusion of Theorem 11 (p.21, used on p.22 and p.28):
nondegeneracy of every vertex of `𝒫` with `z > 0`, `p < P`, `r < R`. Algorithm 1 is encoded by
`IsLemkePath`; "terminates in finite time" is (A), "at a competitive equilibrium" is (B). -/
theorem algorithm1_terminates_at_competitiveEquilibrium {N M : Type*} [Fintype N] [Fintype M] (I : Instance N M)
    (hI : StandingAssumptions I) (P : ℝ) (hP : 0 < P) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ δ : M → ℝ, IsAdmissibleDelta I δ → ∀ ε : ℝ, 0 < ε →
      NondegenerateInRegion I P R δ ε →
      (∃ (w : ℕ → LCPVar I) (T : ℕ), IsLemkePath I P R δ ε w T ∧ zv (w T) = 0) ∧
      ∀ (w : ℕ → LCPVar I) (T : ℕ), IsLemkePath I P R δ ε w T → zv (w T) = 0 →
        (∀ j, pv (w T) j < P) ∧ (∀ i, rv (w T) i < R) ∧
          IsCompetitiveEquilibrium I (decodePrice I P (pv (w T)))
            (decodeAlloc I P (w T)) := by sorry

end MixedManna
