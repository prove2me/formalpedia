-- Prove2me | Theorems.Thm_MinimalAccess_claim_1
-- name    : MinimalAccess.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:07.141755+00:00
-- url     : https://prove2.me/theorems/152a55fc-7498-431c-a7b5-f7dd8024afdf
-- title:
--   Claim 1 (Transformation Claim) — reduce to problems where differing students find one school acceptable
-- statement:
--   Throughout, $I$ is a finite set of students, $S$ a finite set of schools with capacities $q=(q_s)_{s\in S}$, $P=(P_i)_{i\in I}$ strict preferences over $S\cup\{\emptyset\}$ ($\emptyset$ the no-school option, $R_i$ the weak version of $P_i$), $\succ=(\succ_s)_{s\in S}$ strict priorities over $I$, and $r=(r(i))_{i\in I}$ minimal-access rights, $r(i)\subseteq S$.
--
--   Let $\varphi$ be a minimal-access stable and strategy-proof mechanism, and let $\gamma$ be the deferred acceptance mechanism. Let $(P,\succ,r)$ be a problem with $\varphi(P,\succ,r)\neq\gamma(P,\succ,r)$. Then there is a preference profile $\bar P$ such that
--
--   1. (t.a) $\varphi(\bar P,\succ,r)\neq\gamma(\bar P,\succ,r)$, and
--   2. (t.b) for each student $\ell$ with $\varphi_\ell(\bar P,\succ,r)\neq\gamma_\ell(\bar P,\succ,r)$, exactly one school is acceptable under $\bar P_\ell$.
--
--   This is the first step of the uniqueness part of Theorem 1.
--
--   Differences from the source:
--   - encoding: finite sets I, S; no-school option ∅; strict preferences P_i over S ∪ {∅}; strict priorities ≻_s over I → I = Fin n, S = Fin m, ∅ = none; P i : Option (Fin m) ≃ Fin (m+1) and pri s : Fin n ≃ Fin n rank bijections, rank 0 most preferred / highest priority; reason: finite relabelling; every strict order is exactly one rank bijection, so the problems are the same
--   - encoding: γ(P, ≻, r): the student-proposing deferred acceptance algorithm on (P, ≻^r), Steps 0, 1, 2, … (pp.6–7) → gamma q P pri r = published GaleShapley1962.Admissions.Market.deferredAcceptance on the market with acceptable lists best first, all students ordered by adjKey pri r, quotas q; reason: the published procedure runs exactly these simultaneous rounds (fuel-bounded); same outcome
--   - encoding: a mechanism selects a matching φ(P, ≻, r) for each problem → φ : Mechanism n m (a function of (P, pri, r) to assignments) with the hypothesis IsMechanism q φ (every output respects the capacities); reason: the same mechanisms; condition (iii) of a matching holds by the assignment encoding
--   - generalization: context: φ minimal-access stable, strategy-proof and minimal-access monotonic → φ minimal-access stable and strategy-proof (minimal-access monotonicity not assumed); reason: the claim and its proof do not use monotonicity; the source's case is a special case
--   - generalization: capacities q_s ∈ N, positive (cf. q_s ≥ 1, p.29) → q : Fin m → ℕ, q_s = 0 allowed; reason: the statement for positive capacities is the special case; the argument never uses positivity
-- source:
--   Klaus–Klijn, Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism, BSE Working Paper 1264 (rev. July 2023), Appendix A, Claim 1 (Transformation Claim), p.22

import Mathlib
import Definitions.Def_MinimalAccess_Model
import Definitions.Def_MinimalAccess_AdjustedPriorities
import Definitions.Def_MinimalAccess_DeferredAcceptance
import Definitions.Def_MinimalAccess_Mechanism

namespace MinimalAccess

open GaleShapley1962.Admissions

/-- Klaus–Klijn, BSE Working Paper 1264 (rev. July 2023), Appendix A, Claim 1 (Transformation
Claim), p.22, in the context "Let φ satisfy minimal-access stability, strategy-proofness, and
minimal-access monotonicity": "Let (P, ≻, r) such that φ(P, ≻, r) ≠ γ(P, ≻, r). Then, there is a
preference profile P̄ such that (t.a.) φ(P̄, ≻, r) ≠ γ(P̄, ≻, r) and (t.b.) for each student ℓ with
φ_ℓ(P̄, ≻, r) ≠ γ_ℓ(P̄, ≻, r), only one school is acceptable under P̄_ℓ."

**Formalization Note.** `φ` is a mechanism (`IsMechanism q φ`) that is minimal-access stable
and strategy-proof; minimal-access monotonicity, part of the appendix's standing context, is not
assumed (the claim does not use it). "Only one school is acceptable" is
`∃! s, P̄_ℓ(s) < P̄_ℓ(∅)`. Students `Fin n`, schools `Fin m`, `none` = ∅. -/
theorem claim_1 {n m : ℕ} (q : Fin m → ℕ) (φ : Mechanism n m) (hφ : IsMechanism q φ)
    (hMAS : IsMinimalAccessStableMech q φ) (hSP : IsStrategyProof φ)
    (P : Fin n → Pref m) (pri : Fin m → Prio n) (r : Fin n → Finset (Fin m))
    (hne : φ P pri r ≠ gamma q P pri r) :
    ∃ Pbar : Fin n → Pref m, φ Pbar pri r ≠ gamma q Pbar pri r ∧
      ∀ ℓ, φ Pbar pri r ℓ ≠ gamma q Pbar pri r ℓ → ∃! s, Acceptable Pbar ℓ s := by sorry

end MinimalAccess
