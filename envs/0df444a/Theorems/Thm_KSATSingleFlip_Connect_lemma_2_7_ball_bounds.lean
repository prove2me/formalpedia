-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_2_7_ball_bounds
-- name    : KSATSingleFlip.Connect.lemma_2_7_ball_bounds
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:14:35.059243+00:00
-- url     : https://prove2.me/theorems/656d8be9-59be-40c2-aab8-f08fe40a1707
-- title:
--   Bounded-degree factor-ball cardinality bounds
-- statement:
--   Let every clause have at most $k$ variables, with $k,r,D\ge1$, and set $$M_{r,D}=\sum_{h=0}^{r+1}(kD)^h.$$ If the radius-$2r$ factor ball around a variable $v$ is a tree and every variable in it has full-formula degree at most $D$, then the number of variable and clause vertices in that ball is at most $M_{r,D}$. For any fixed variable $u$, at most $M_{r,D}$ such locally tree-structured balls contain $u$. These are the two cardinality statements in (2.1); the separate clause-insertion/deletion sensitivity statement of Lemma 2.7 is not included.
-- source:
--   Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.7, equation (2.1), printed pp. 12–13 (PDF pp. 14–15), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_FactorGraph

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- The two cardinality bounds in (2.1) of Lemma 2.7. The separate
clause-insertion sensitivity conclusion is not part of this target. -/
theorem lemma_2_7_ball_bounds {n : ℕ} (Φ : GFormula (Fin n)) (k r D : ℕ)
    (hk : 1 ≤ k) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ k) :
    (∀ v, LocallyTree Φ v r D →
      (ballVars Φ v r).card + (ballIdx Φ v r).card ≤
        ∑ h ∈ Finset.range (r + 2), (k * D)^h) ∧
    (∀ u, (Finset.univ.filter fun v : Fin n =>
      LocallyTree Φ v r D ∧ u ∈ ballVars Φ v r).card ≤
        ∑ h ∈ Finset.range (r + 2), (k * D)^h) := by
  sorry

end KSATSingleFlip.Connect
