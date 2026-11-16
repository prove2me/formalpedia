-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_lemma_4_1
-- name    : MeanCertificates1424.Hardness.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:00:58.460067+00:00
-- url     : https://prove2.me/theorems/6aa95a06-b6ee-44cd-b81c-8f46a5367630
-- title:
--   Lemma 4.1 — decomposition into compact honest components
-- statement:
--   For an instance of §2 (real reports, nonnegative normalized weights, finite audit intervals), with $h=n-b$,
--   $$C_I(y)=\bigcup_{|H|=h}P_H.$$
--   If $b<n$ or $Q\ne\emptyset$, every component $P_H$ with $|H|=h$ is a compact polytope (a bounded intersection of finitely many closed half-spaces), and a nonempty feasible class attains both endpoints $\ell_I(y)$ and $u_I(y)$ at feasible fields.
--
--   The decomposition is the starting point of the alphabet theory of §4.
--
--   Differences from the source: none.
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Lemma 4.1, printed p.12 (PDF p.14)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_General

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Lemma 4.1, printed p.12 / PDF p.14. `C_I(y) = ⋃_{|H| = h} P_H`; if `b < n` or `Q ≠ ∅`,
every `P_H` with `|H| = h` is a compact polytope, and a nonempty feasible class attains both
endpoints. -/
theorem lemma_4_1 (I : Inst) (hI : Valid I) :
    CI I = ⋃ H ∈ {H : Finset (Fin I.n) | H.card = I.n - I.budget}, PH I H ∧
    (Anchored I →
      (∀ H : Finset (Fin I.n), H.card = I.n - I.budget → IsCompactPolytope (PH I H)) ∧
      ((CI I).Nonempty →
        (∃ x ∈ CI I, (wmean I x : EReal) = upper I) ∧
        (∃ x ∈ CI I, (wmean I x : EReal) = lower I))) := by sorry

end MeanCertificates1424.Hardness.Supplement
