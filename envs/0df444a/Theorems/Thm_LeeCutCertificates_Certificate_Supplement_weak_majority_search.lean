-- Prove2me | Theorems.Thm_LeeCutCertificates_Certificate_Supplement_weak_majority_search
-- name    : LeeCutCertificates.Certificate.Supplement.weak_majority_search
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:12:01.353331+00:00
-- url     : https://prove2.me/theorems/45059d45-e434-4599-8715-737a0b6c1aa9
-- title:
--   Lemma 48 — Weak majority search
-- statement:
--   Let $T$ be a supplied rooted tree on $n\ge1$ vertices and let the known total mass be $D>0$. A deterministic subset-mass oracle program is selected before the nonnegative vertex weights $w$, and works for every such $w$ with total $D$. It returns endpoints $x,y$ such that
--
--   $$\mu(\operatorname{subtree}(v))\ge D/2\ \Longleftrightarrow\ v\in[\mathrm{root},x]\cup[\mathrm{root},y]$$
--
--   for every vertex $v$, using at most $8(\lfloor\log_2n\rfloor+1)$ measure evaluations on every answer path. Endpoints may coincide. The cover is exact, including equality at $D/2$, and supplies the weak-interest searches for Theorem 52.
--
--   **Formalization Note** On a finite set every nonnegative additive measure equals the sum of its singleton masses. Only subset sums are supplied to the program. The rooted-tree type ensures $n\ge1$. Appendix A, printed p.56 (PDF p.57), supplies the coefficient 8.
--
--   Differences from the source:
--   - encoding: an arbitrary undirected supplied tree → a public root and parent map reaching that root; reason: every finite tree can be rooted offline; parent edges count each unordered edge once
--   - encoding: a finite nonnegative additive measure and O(log n) evaluations → nonnegative vertex masses behind a subset-sum oracle, known total D>0, and cap 8(floor(log₂ n)+1); reason: finite additivity is exactly the singleton-sum representation; Appendix A gives the cap
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Lemma 48, printed p.48 (PDF p.49); Appendix A, printed pp.53–56 (PDF pp.54–57)

import Definitions.Def_LeeCutCertificates_Certificate_Supplement_OraclePrograms
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_MeasureSearch

set_option autoImplicit false

namespace LeeCutCertificates.Certificate.Supplement

theorem weak_majority_search (n : ℕ) (T : RootedTree n) (D : ℝ) (hD : 0 < D) :
    ∃ p : OracleProgram (Finset (Fin n)) (Fin n × Fin n),
      p.Capped (8 * (Nat.log 2 n + 1)) ∧
      ∀ w : Fin n → ℝ, (∀ v, 0 ≤ w v) → subsetMass w Finset.univ = D →
        WeakHeavyCover T w D (p.run (subsetMass w)).1 := by sorry

end LeeCutCertificates.Certificate.Supplement
