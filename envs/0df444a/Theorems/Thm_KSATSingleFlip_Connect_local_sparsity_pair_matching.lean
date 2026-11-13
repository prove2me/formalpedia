-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_local_sparsity_pair_matching
-- name    : KSATSingleFlip.Connect.local_sparsity_pair_matching
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:41:24.798461+00:00
-- url     : https://prove2.me/theorems/93e29036-ef73-49b9-bf98-583e07fc5cf9
-- title:
--   Local sparsity implies a pair matching
-- statement:
--   Let $\Phi$ be a finite Boolean formula with nonempty clause scopes on $n$ variables, and suppose $k\ge4$ and the local sparsity condition $\operatorname{LS}(k,\Phi)$ of Definition 7.2(ii) holds. If $J$ is a family of clause occurrences with
--
--   $$2|J|\le\rho(k)n,$$
--
--   then each clause occurrence in $J$ can be assigned two distinct variables from its scope, with the assigned pairs disjoint across different occurrences. This isolates the Hall matching step in the proof of Lemma 7.12 and permits repeated clauses as distinct occurrences.
-- source:
--   Wang, Yin, Yu, and Zhang, Single-Variable Connectivity in Random k-SAT, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf, proof of Lemma 7.12, printed p. 64; slightly generalized Hall argument.

import Definitions.Def_KSATSingleFlip_Connect_Repair

namespace KSATSingleFlip.Connect

/-- Local sparsity yields a pair matching for every sufficiently small clause family. -/
theorem local_sparsity_pair_matching {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (hk : 4 ≤ k) (hscope : ∀ c : Fin Φ.length, (vbl (Φ.get c)).Nonempty)
    (hLS : LS k Φ) (J : Finset (Fin Φ.length))
    (hsmall : (2 * J.card : ℝ) ≤ rho k * n) :
    ∃ M : Fin Φ.length → Finset (Fin n), IsPairMatching Φ J M := by sorry

end KSATSingleFlip.Connect
