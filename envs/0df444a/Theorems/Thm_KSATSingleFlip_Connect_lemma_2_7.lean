-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_2_7
-- name    : KSATSingleFlip.Connect.lemma_2_7
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:21:11.102066+00:00
-- url     : https://prove2.me/theorems/2cf70283-7629-4e38-b42a-6fb5b25f9540
-- title:
--   Lemma 2.7 — Bounded-degree ball sensitivity
-- statement:
--   Let $k,r,D\ge1$, every clause have at most $k$ variables, and $M_{r,D}=\sum_{h=0}^{r+1}(kD)^h$. A locally tree-structured radius-$2r$ factor ball has at most $M_{r,D}$ vertices, and any variable lies in at most $M_{r,D}$ such balls. Appending one clause with at most $k$ variables changes at most $2kM_{r,D}$ trimmed balls. Hence any sum of $[0,1]$-valued root-dependent observables of those balls changes by at most the same amount. Trimmed-ball data retains variable identities, original clause-occurrence labels and signed clauses; appending fixes old labels, and reversing the comparison covers deletion.
-- source:
--   Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.7 and (2.1), printed pp. 12–13 (PDF pp. 14–15), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_TrimmedBall

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- Lemma 2.7: bounded-degree factor balls and one-clause sensitivity. -/
theorem lemma_2_7 {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) (k r D : ℕ)
    (hk : 1 ≤ k) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ k) (hC : (vbl C).card ≤ k) :
    (∀ v, LocallyTree Φ v r D →
      (ballVars Φ v r).card + (ballIdx Φ v r).card ≤
        ∑ h ∈ Finset.range (r + 2), (k * D)^h) ∧
    (∀ u, (Finset.univ.filter fun v : Fin n =>
      LocallyTree Φ v r D ∧ u ∈ ballVars Φ v r).card ≤
        ∑ h ∈ Finset.range (r + 2), (k * D)^h) ∧
    ((Finset.univ.filter fun v : Fin n =>
      trimmedBall Φ v r D ≠ trimmedBall (Φ ++ [C]) v r D).card ≤
        2 * k * ∑ h ∈ Finset.range (r + 2), (k * D)^h) ∧
    (∀ f : Fin n → Option (Finset (Fin n) × Finset ℕ × GFormula (Fin n)) → ℝ,
      (∀ v b, 0 ≤ f v b ∧ f v b ≤ 1) →
      |(∑ v, f v (trimmedBall Φ v r D)) -
        (∑ v, f v (trimmedBall (Φ ++ [C]) v r D))| ≤
        (2 * k * ∑ h ∈ Finset.range (r + 2), (k * D)^h : ℕ)) := by
  sorry

end KSATSingleFlip.Connect
