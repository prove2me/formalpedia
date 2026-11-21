-- Prove2me | Theorems.Thm_GRH_centered_moebius_progression_bilinear_power_bound
-- name    : GRH.centered_moebius_progression_bilinear_power_bound
-- status  : Open
-- author  : @pragyan
-- created : 2026-11-21T01:51:16.720473+00:00
-- url     : https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006
-- title:
--   Möbius bilinear cancellation in centered progression-count errors
-- statement:
--   Fix $q\ge1$, a unit residue $a\bmod q$, and $1/2<\sigma<1$. Let $U=\lfloor\sqrt N\rfloor$ and let $A_{d,e}(N;q,a)$ count positive $r\le\lfloor N/(de)\rfloor$ with $der\equiv a\pmod q$. The proposed open estimate asks for $C=C(q,a,\sigma)\ge0$ such that for all $N\ge0$,
--   $$\left|\sum_{1\le d,e\le U}\mu(d)\mu(e)\left(A_{d,e}(N;q,a)-\mathbf1_{(de,q)=1}\frac{N}{qde}\right)\right|\le C(N+1)^\sigma.$$
--   For invertible $d,e$ the subtracted term is the main term of a single arithmetic-progression count; for noninvertible $de$ the count is zero because $a$ is a unit. The centered quantity isolates signed cancellation in these counting errors after removing the separable principal main term. This remains a conjectural analytic estimate, rather than a claim that a pointwise $O(1)$ counting error alone suffices.
-- source:
--   Proposed centered-error subproblem of GRH.moebius_reduced_progression_bilinear_power_bound, https://prove2.me/theorems/1e39fbca-7acc-40a2-baab-ab807852220a. The exact finite bilinear truncation is adapted from Helfgott–Thompson, Summing μ(n): a faster elementary algorithm, §2, equations (2.1)–(2.2), https://doi.org/10.1007/s40993-022-00408-8. Subtracting N/(qde) is the elementary progression-count main term. The displayed signed cancellation estimate is a new proposed open subproblem, not an estimate asserted in the cited paper.

import Definitions.Def_GRH_MoebiusBilinear

theorem GRH.centered_moebius_progression_bilinear_power_bound
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |GRH.centeredMoebiusBilinear q a N| ≤ C * ((N : ℝ) + 1) ^ σ := by sorry
