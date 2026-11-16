-- Prove2me | Theorems.Thm_LeeCutCertificates_Certificate_Supplement_deterministic_all_mincuts
-- name    : LeeCutCertificates.Certificate.Supplement.deterministic_all_mincuts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:06:25.021226+00:00
-- url     : https://prove2.me/theorems/678d96d4-a961-4ca7-a122-ac3e021647b5
-- title:
--   Theorem 4 — Deterministic weighted minimum cut
-- statement:
--   There is an absolute positive integer $C$, fixed before $n$, such that for every $n\ge2$ one deterministic cut-oracle program returns, for every nonnegative real weighted graph $G$, its exact value $\lambda(G)$ and exactly all of its minimum-cut shores. Every answer path has at most
--
--   $$C\,n(\lfloor\sqrt n\rfloor+1)L(n)^3K(n)^2$$
--
--   queries, giving the source's $O(n^{3/2}\log^3(2n)(\log\log(2n))^2)$ rate. When $\lambda(G)=0$, the output also returns exactly the positive-support component partition; its nonempty proper unions are precisely the minimum-cut shores. Both orientations are reported, including for $n=2$ and the all-zero graph. This companion theorem is not used in the proof of the certificate goal.
--
--   **Formalization Note** The cap is §11.8's public cap, printed p.42 (PDF p.43). $L(n)=\max\{1,\lceil\log_2(2n)\rceil\}$ and $K(n)=L(L(n))$. The absolute constant covers the bounded small-$n$ reconstruction branch as well as all reporting calls; it cannot depend on weights or output size.
--
--   Differences from the source:
--   - encoding: finite graph vertices and exact deterministic query access → Fin n, the immutable real-capacity graph interface, and a well-founded OracleProgram selected before every hidden graph; reason: finite relabeling and explicit query traces preserve all instances; caps apply to every answer function
--   - encoding: the stated big-O query rate → one absolute positive C and the public cap C n (floor(sqrt n)+1) L(n)^3 K(n)^2; reason: §11.8 and Appendix A give this cap; L≤3 ln(2n) and K≤7 ln ln(2n) recover the exact asymptotic
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), Theorem 4, printed p.7 (PDF p.8); Appendix A, printed pp.53–56 (PDF pp.54–57)

import Definitions.Def_LeeCutCertificates_Certificate_Supplement_GraphAlgorithms
import Definitions.Def_LeeCutCertificates_Certificate_Supplement_Budgets

set_option autoImplicit false
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate.Supplement

theorem deterministic_all_mincuts :
    ∃ C : ℕ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n →
      ∃ p : OracleProgram (Finset (Fin n)) (AllCutsOutput n),
        p.Capped (C * n * (Nat.sqrt n + 1) * logL n ^ 3 * logK n ^ 2) ∧
        ∀ (m : ℕ) (G : Graph n m), Nonnegative G →
          CorrectAllCuts G (p.run (cutw G)).1 := by sorry

end LeeCutCertificates.Certificate.Supplement
