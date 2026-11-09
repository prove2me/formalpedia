-- Prove2me | Theorems.Thm_MajorityDepthThree_Exact_sharp_threshold_count
-- name    : MajorityDepthThree.Exact.sharp_threshold_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:35.461518+00:00
-- url     : https://prove2.me/theorems/36e43ce7-b960-4e94-834c-cbfaf0b0d162
-- title:
--   Theorem 1.4 — full threshold counting and central sharpness
-- statement:
--   For every integer $0\le t\le n$ and every valid signed $t$-threshold 3-CNF $F$ on $n$ variables,
--
--   $$\theta_t(F)\le 2^t(3/2)^{(n-t)/2}.$$
--
--   Separately, every $\lfloor n/2\rfloor$-threshold 3-CNF satisfies
--
--   $$\theta_{\lfloor n/2\rfloor}(F)\le6^{n/4}.$$
--
--   For each $n$ divisible by four there exists such a formula with equality; the witness can be chosen monotone. This includes $n=0$. The first conclusion covers the entire range $t\le n$ and imposes no monotonicity. The central specialization and its equality witness are part of the same item, providing both the sharp counting bound and its attainment.
--
--   Differences from the source:
--   - encoding: n Boolean variables → The fixed carrier Fin n with ambient set univ; reason: Relabeling preserves clauses, assignments, weights and top fan-in; the theorem retains its stated parameter domain
--   - reading: The in-particular sentence reuses F after the arbitrary-t assertion → A separate universal quantifier over central-threshold formulas; reason: It specializes the theorem to t=floor(n/2); a clause-free n=8 formula is 0-threshold and has 70 weight-four assignments, exceeding 36
--   - generalization: Equality attainable whenever 4 divides n → An explicitly monotone equality witness whenever 4 divides n; reason: The source supplies disjoint copies of the monotone four-variable three-clique; forgetting monotonicity gives the displayed claim
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), p.4, Theorem 1.4; pp.8–10, clique construction and disjoint copies

import Definitions.Def_MajorityDepthThree_Exact_Restrictions
import Definitions.Def_MajorityDepthThree_Exact_Circuits

set_option autoImplicit false

namespace MajorityDepthThree.Exact

theorem sharp_threshold_count  :
    (∀ (n t : ℕ) (F : CNF (Fin n)), t ≤ n → ValidCNF Finset.univ F →
      Width 3 F → Threshold Finset.univ F t →
      (theta Finset.univ F t : ℝ) ≤ countingBound n t) ∧
    (∀ (n : ℕ) (F : CNF (Fin n)), ValidCNF Finset.univ F → Width 3 F →
      Threshold Finset.univ F (n / 2) →
      (theta Finset.univ F (n / 2) : ℝ) ≤ (6 : ℝ) ^ ((n : ℝ) / 4)) ∧
    (∀ n : ℕ, 4 ∣ n → ∃ F : CNF (Fin n),
      ValidCNF Finset.univ F ∧ Width 3 F ∧ Monotone F ∧ Threshold Finset.univ F (n / 2) ∧
      (theta Finset.univ F (n / 2) : ℝ) = (6 : ℝ) ^ ((n : ℝ) / 4)) := by sorry

end MajorityDepthThree.Exact
