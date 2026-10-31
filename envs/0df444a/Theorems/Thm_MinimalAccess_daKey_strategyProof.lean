-- Prove2me | Theorems.Thm_MinimalAccess_daKey_strategyProof
-- name    : MinimalAccess.daKey_strategyProof
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:18.592595+00:00
-- url     : https://prove2.me/theorems/53299e93-db18-4ca3-81c2-8cf3f433c80a
-- title:
--   Classical student-proposing deferred acceptance is strategy-proof (Dubins–Freedman, Roth)
-- statement:
--   Let $I$, $S$ be finite sets of students and schools with capacities $q$, let $P$ be a profile of strict student preferences over $S\cup\{\emptyset\}$, and let $\succ'$ be any profile of strict school priorities over $I$. Write $\gamma(P,\succ')$ for the outcome of student-proposing deferred acceptance on the classical problem $(P,\succ')$. For every student $i$ and every strict preference $P'_i$,
--
--   $$
--   \gamma_i(P,\succ')\;R_i\;\gamma_i(P'_i,P_{-i},\succ').
--   $$
--
--   The paper cites Dubins–Freedman (1981) and Roth (1982) and applies the result at $\succ'=\succ^r$ to show that $\gamma$ is strategy-proof (proof of Lemma 1).
--
--   Differences from the source:
--   - encoding: finite sets I, S; no-school option ∅; strict preferences P_i over S ∪ {∅}; strict priorities ≻_s over I → I = Fin n, S = Fin m, ∅ = none; P i : Option (Fin m) ≃ Fin (m+1) and pri s : Fin n ≃ Fin n rank bijections, rank 0 most preferred / highest priority; reason: finite relabelling; every strict order is exactly one rank bijection, so the problems are the same
--   - encoding: strict priority profile ≻′ of the classical problem → key profile key : Fin m → Fin n → ℕ with every key s injective; γ(P, ≻′) = daKey q P key; reason: every strict order is given by injective keys and conversely
--   - generalization: the cited fact used at ≻′ = ≻^r → stated for every injective key profile; reason: the cited theorem is the general classical statement; ≻^r = adjKey pri r is a special case
--   - generalization: capacities q_s ∈ N, positive (cf. q_s ≥ 1, p.29) → q : Fin m → ℕ, q_s = 0 allowed; reason: the statement for positive capacities is the special case; the argument never uses positivity
-- source:
--   Klaus–Klijn, Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism, BSE Working Paper 1264 (rev. July 2023), proof of Lemma 1, p.12 (citing Dubins and Freedman 1981, Roth 1982)

import Mathlib
import Definitions.Def_MinimalAccess_Model
import Definitions.Def_MinimalAccess_AdjustedPriorities
import Definitions.Def_MinimalAccess_DeferredAcceptance

namespace MinimalAccess

open GaleShapley1962.Admissions

/-- Klaus–Klijn, BSE Working Paper 1264 (rev. July 2023), proof of Lemma 1, p.12: "Then, it
follows from Dubins and Freedman (1981) and Roth (1982) that γ_i(P, ≻, r) = γ_i(P, ≻^r) R_i
γ_i(P′_i, P_{-i}, ≻^r) = γ_i(P′_i, P_{-i}, ≻, r). Hence, γ is strategy-proof." The cited fact
is strategy-proofness of classical student-proposing deferred acceptance for every strict
priority profile, stated here for every injective key profile `key` (the paper applies it at
`key = adjKey pri r`).

**Formalization Note.** `daKey q P key` is the classical deferred acceptance outcome `γ(P, key)`;
`Function.update P i P'` is `(P′_i, P_{-i})`; the comparison `R_i` uses the **true** `P i`.
Each `key s` is injective, so it is a strict priority order. Any capacities, including `0`. -/
theorem daKey_strategyProof {n m : ℕ} (q : Fin m → ℕ) (key : Fin m → Fin n → ℕ)
    (hkey : ∀ s, Function.Injective (key s)) (P : Fin n → Pref m) (i : Fin n) (P' : Pref m) :
    P i (daKey q P key i) ≤ P i (daKey q (Function.update P i P') key i) := by sorry

end MinimalAccess
