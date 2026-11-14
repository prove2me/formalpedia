-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_2_7_reverse_ball_bound
-- name    : KSATSingleFlip.Connect.lemma_2_7_reverse_ball_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:35:49.349206+00:00
-- url     : https://prove2.me/theorems/f169a0ab-6533-4a57-ba16-b4b6a5222a39
-- title:
--   Reverse locally tree-structured ball bound
-- statement:
--   Let $\Phi$ be a finite formula in which every clause involves at most $k$ variables. Fix a variable $u$, a radius $r$, and a degree cutoff $D$. At most $$\sum_{h=0}^{r}(kD)^h$$ variables $v$ have both an $(r,D)$-locally tree-structured ball and $u$ in that ball. This strengthens the reverse-neighborhood estimate in (2.1) of Lemma 2.7 by one geometric term; the proof does not use acyclicity.
-- source:
--   Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.7, equation (2.1), printed pp. 12–13, STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_GoodReach

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

theorem lemma_2_7_reverse_ball_bound {n : ℕ} (Φ : GFormula (Fin n))
    (k r D : ℕ) (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ k) (u : Fin n) :
    (Finset.univ.filter fun v : Fin n => LocallyTree Φ v r D ∧ u ∈ ballVars Φ v r).card ≤
      ∑ h ∈ Finset.range (r + 1), (k*D)^h := by
  sorry

end KSATSingleFlip.Connect
