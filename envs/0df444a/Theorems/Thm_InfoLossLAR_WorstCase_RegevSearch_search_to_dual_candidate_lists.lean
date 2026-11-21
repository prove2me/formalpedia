-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_search_to_dual_candidate_lists
-- name    : InfoLossLAR.WorstCase.RegevSearch.search_to_dual_candidate_lists
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T02:26:07.021008+00:00
-- url     : https://prove2.me/theorems/98258395-a948-48ad-91ba-ef2767f47f76
-- title:
--   A polynomial-size list of dual decoding candidates from fixed-family search
-- statement:
--   Suppose a uniform quantum algorithm solves search on fresh tables from the prescribed LWE family on all sufficiently large dimensions in an infinite set $S$. Assume the simultaneous variance-grid estimate for all stages of the modular recursion. There is a uniform quantum family and a polynomial $P$ such that the following holds for all sufficiently large $n\in S$. Given a nonsingular integer basis $B$, rational $R>\sqrt2\,q_n\eta_{\varepsilon_n}(B\mathbb Z^n)$, a fixed rational query $x$ and unary accuracy $k$, the family receives $P(n)$ independent Gaussian coefficient samples at width $R$. If $B^\top u=z\in\mathbb Z^n$ and $R^2\|x-u\|^2<\sigma_n^2/4$, the measured word begins with an encoding of a finite list containing $(u,z)$ except with probability at most $e(n)+1/(k+1)$, for a negligible $e$. The probability averages the pool and the circuit measurement. Additional candidates may occur in any order.
-- source:
--   Construction subproblem for InfoLossLAR.WorstCase.RegevSearch.search_to_shared_pool_bdd, https://prove2.me/theorems/0bf36425-687f-493d-a04f-ac2e81e7e02e. Based on the modular BDD recursion and search-table reduction of Regev, §3.2.1, Lemmas 3.5, 3.7 and 3.11, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. List output, the fixed-family integer Gaussian and the shared pool are the construction obligations of this specialization.

import Definitions.Def_InfoLossLAR_RegevSearch_SharedPoolBDD

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open RegevLWE.GaussConv
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch

theorem search_to_dual_candidate_lists
    (hgrid : ∀ (s q M : ℕ), 2 ≤ s → 2 ≤ q → 0 < M → ∀ E : ℝ, 0 ≤ E → E ≤ (s : ℝ)^2 / 2 →
    ∃ i : Fin (M + 1), ∀ j : ℕ,
      let den : ℚ := (q : ℚ)^(2*j)
      let v : ℚ := (s : ℚ)^2 - ((s : ℚ)^2/2) * (i.val : ℚ) / M / den
      let total := E / (den : ℝ) + (v : ℝ)
      let mass := fun (width : ℝ) (z : ℤ) => AFT.GaussianSource.weight width z /
        AFT.GaussianSource.realNormalizer width
      (s : ℚ)^2/2 ≤ v ∧ v ≤ (s : ℚ)^2 ∧
      0 ≤ (s : ℝ)^2 - total ∧
      (s : ℝ)^2 - total ≤ (s : ℝ)^2 / (2 * M * (den : ℝ)) ∧
      (∑' z : ℤ, |mass (Real.sqrt total) z - mass (s : ℝ) z|)/2 ≤
        1 / ((M : ℝ) * (den : ℝ)))
    (S : Set ℕ) (hS : S.Infinite) (hpos : ∀ n ∈ S, 1 ≤ n)
    (A : MFamily) (hA : IsMQPT A) (samples : Polynomial ℕ) (cutoff : ℕ)
    (hsearch : SearchOn A samples cutoff S) :
    ∃ T : MFamily, IsMQPT T ∧ ∃ P : Polynomial ℕ, ∃ e : ℕ → ℝ, Negligible e ∧
      ∃ N : ℕ, ∀ n ∈ S, N ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
      ∀ R : ℚ, 0 < R →
        Real.sqrt 2 * (famq n : ℝ) * smoothingParam (inputModule B) (smoothingError n) < (R : ℝ) →
      ∀ (k : ℕ) (x u : Fin n → ℚ) (z : Fin n → ℤ),
        (∀ j, ∑ i, (B i j : ℚ) * u i = (z j : ℚ)) →
        (R : ℝ)^2 * (∑ i, (((x i-u i : ℚ) : ℝ))^2) < (famσ n : ℝ)^2 / 4 →
        (∑' pool : Fin (P.eval n) → Fin n → ℤ,
          (∏ j, coefficientMass B (R : ℝ) (pool j)) *
          outputProb T (poolBDDInput B R k pool x) (fun out => ¬ ∃ vs : List (List ℚ × List ℤ),
            encL (fun p : List ℚ × List ℤ => encPair (encL encQ p.1) (encL encI p.2)) vs <+: out ∧
              (List.ofFn u,List.ofFn z) ∈ vs)) ≤ e n + 1 / ((k : ℝ)+1) := by
  sorry

end InfoLossLAR.WorstCase.RegevSearch
