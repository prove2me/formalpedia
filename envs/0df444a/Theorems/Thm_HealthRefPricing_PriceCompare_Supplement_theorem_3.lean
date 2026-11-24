-- Prove2me | Theorems.Thm_HealthRefPricing_PriceCompare_Supplement_theorem_3
-- name    : HealthRefPricing.PriceCompare.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:39:53.73537+00:00
-- url     : https://prove2.me/theorems/c9c98e74-cfec-4ff3-8f18-743d574b33c9
-- title:
--   Theorem 3 (corrected: endpoints and equality case) — endogenous reference pricing equilibria
-- statement:
--   Under the published standing assumptions $m>0$, $\gamma>0$, $c\ge0$, $a_1\le a_2$, $\tilde c<c$, consider the endogenous-reference-pricing game. Let
--
--   $$B=e^{u_0}+e^{a_1-\gamma\tilde c},\quad E=e^{a_2-\gamma\tilde c},\quad L=c+\frac{B+E}{\gamma B},\quad U=c+\frac{B+E}{\gamma E}.$$
--
--   1. If $E\le B$, a price vector is an ERP Nash equilibrium if and only if $p_1=p_2\in[L,U]$. There are infinitely many equilibria when $E<B$. When $E=B$, there is exactly one equilibrium, at the common price $L=U$.
--   2. If $B<E$, there is exactly one ERP Nash equilibrium. It has $p_1<p_2$, satisfies
--
--   $$e^{a_2-\gamma(p_2-p_1+\tilde c)}=B[\gamma(p_2-c)-1],\tag{8}$$
--   $$\gamma(p_1-c)-1=\frac{1}{\gamma(p_2-c)-1},\tag{9}$$
--
--   and is the unique solution of (8)–(9) over all real price pairs.
--
--   This companion theorem classifies equilibria when providers jointly determine the reference price through their minimum price. It is not used in the proof of the mission's Proposition 5 goal.
--
--   **Formalization Note** Providers use `Fin 2`: index 0 is provider 1 and index 1 provider 2. The stored exogenous reference price is unused, including during deviations. All equilibrium assertions use the published pure-Nash relation. The two boundary corrections and the removal of Assumption 3 are recorded with evidence in DISPROOF.md and MODERATION_NOTES.md.
--
--   Differences from the source:
--   - correction: Theorem 3 prints an open symmetric-price interval → the equilibrium set is exactly the diagonal over the closed interval [L,U]; reason: Appendix p. 11 (PDF 44) has non-strict best-response comparisons; for m=γ=c=1, ct=u0=a1=a2=0 both endpoints L=5/2 and U=4 are equilibria, excluded by the printed interval.
--   - correction: infinitely many equilibria under B≥E, including B=E → infinitely many only if E<B, and exactly one if E=B; reason: when E=B the corrected interval collapses to L=U=c+2/γ; for m=γ=c=1, ct=u0=a1=0, a2=log 2 the unique equilibrium is (3,3).
--   - generalization: §6.1 imposes Assumption 3 on limiting ERP best-response shares → no Assumption 3 hypothesis; reason: own log-profit is strictly concave on each side of the rival price, with a downward derivative jump there; the best-response classification on Appendix p. 11 does not require the share bound, so the result specializes to all instances satisfying Assumption 3.
--   - encoding: two providers with prices above common treatment cost and the standing model conventions → Fin 2, all real prices and deviations, and published Standing (m>0, γ>0, c≥0, a1≤a2, ct<c); reason: index 0 denotes provider 1; a price ≤c earns ≤0 whereas every price >c earns >0, preserving exactly the equilibria; nonnegative cost and positive population and sensitivity are the inherited economic conventions.
-- source:
--   Nassiri, Adida & Mamani, Reference pricing for healthcare services, author manuscript (SSRN 3176280, version of Dec. 28, 2020; eScholarship 3sm502rz), p. 20 (PDF 21), Theorem 3, equations (8)–(9); proof, Appendix p. 11 (PDF 44)

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Supplement_ERP

namespace HealthRefPricing.PriceCompare.Supplement

/-- Theorem 3, corrected at the interval endpoints and at equality of the regime threshold.
Assumption 3 is unnecessary for the log-profit best-response argument. -/
theorem theorem_3 (P : Params) (hS : P.Standing) :
    let B := Real.exp P.u0 + Real.exp (P.a 0 - P.γ * P.ct)
    let E := Real.exp (P.a 1 - P.γ * P.ct)
    let L := P.c + (B + E) / (P.γ * B)
    let U := P.c + (B + E) / (P.γ * E)
    (E ≤ B → ∀ p : Fin 2 → ℝ,
      IsEqERP P p ↔ p 0 = p 1 ∧ p 0 ∈ Set.Icc L U) ∧
    (E < B → Set.Infinite {p : Fin 2 → ℝ | IsEqERP P p}) ∧
    (E = B → ∃! p : Fin 2 → ℝ, IsEqERP P p) ∧
    (B < E → (∃! p : Fin 2 → ℝ, IsEqERP P p) ∧
      ∀ p : Fin 2 → ℝ, IsEqERP P p →
        p 0 < p 1 ∧
        Real.exp (P.a 1 - P.γ * (p 1 - p 0 + P.ct)) =
          B * (P.γ * (p 1 - P.c) - 1) ∧
        P.γ * (p 0 - P.c) - 1 = 1 / (P.γ * (p 1 - P.c) - 1) ∧
        ∀ q : Fin 2 → ℝ,
          Real.exp (P.a 1 - P.γ * (q 1 - q 0 + P.ct)) =
            B * (P.γ * (q 1 - P.c) - 1) →
          P.γ * (q 0 - P.c) - 1 = 1 / (P.γ * (q 1 - P.c) - 1) → q = p) := by sorry

end HealthRefPricing.PriceCompare.Supplement
