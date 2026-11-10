-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_7_11
-- name    : KSATSingleFlip.Connect.lemma_7_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:09:08.966811+00:00
-- url     : https://prove2.me/theorems/2090354c-c8ca-49c7-9a5d-1c1e36e30bd5
-- title:
--   Lemma 7.11 — small-set bounds for repair
-- statement:
--   Let $k$ be sufficiently large and $0\le m\le\frac{2^kn}{k}\big(\ln k+\ln\ln k+1+\frac{\ln\ln k+1/2}{\ln k}-\frac{6(\ln\ln k)^2}{(\ln k)^2}\big)$. Fix $x\in\{0,1\}^n$. Let $\Phi_0$ consist of $\mathrm{Pois}(m(1-2^{-k}))$ independent uniform $k$-clauses satisfied by $x$, and independently $G$ of $\mathrm{Pois}(m)$ independent uniform $k$-clauses. With probability at least $1-e^{-\rho^8n}$, for every $\Phi^+$ with $\Phi_0\subseteq\Phi^+\subseteq\Phi_0\cup G$:
--   (i) $\mathrm{NoTree}(B)<\max\{\rho^4n, |B|/(1024(\ln k)^{20})\}$ for every $|B|\le\rho n$;
--   (ii) $|\{C\in C_{\mathrm{force}}:\mathrm{sat}_x(C)\subseteq B\}|\le(\ln k)^8|B|$ for every $\rho^4n\le|B|\le\lceil2\rho n\rceil$;
--   (iii) $\mathrm{ForcingLink}(U)+2\,\mathrm{MultiLink}(U)<(1+1/(4(\ln k)^6))|U|$ for every $\rho^4n\le|U|\le\rho n$.
--
--   Differences from the source:
--   - encoding: Φ⁺ with Φ₀ ⊆ Φ⁺ ⊆ Φ₀ ∪ G → Φ⁺ = (clauses of Φ₀) ++ (sub-formula of G at positions I), with Φ₀ the first positions; reason: every such sub-multiset is of this form up to reordering, and the counts do not depend on the order
--   - reading: no explicit range of n → ∃ n₀, ∀ n ≥ n₀; reason: standing convention of p. 2 (the proof's last union bound is "for large n")
--   - encoding: m ≥ 0 (the Poisson mean) → m : ℝ, 0 ≤ m; reason: Lemma 7.13 applies the lemma at the non-integer m/(1 − 2^{−k})
--   - encoding: M ∼ Pois(m) and then M independent clauses → poisExp/poisProb: the series ∑_M e^{-m} m^M/M! · (uniform average over M-tuples of clauses); reason: same law; the integrands lie in [0,1], so the series converges
--   - encoding: variables [n] = {1,…,n}, formulas as indexed clause collections → variables Fin n; Φ(k,n,m) = uniform law on the published Formula n k m; other formulas are clause lists (position = clause index), sub-formulas are sets of positions; reason: bijective reindexing; repeated clauses stay distinct, as in the paper's indexed collections
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), Lemma 7.11 (with the counts of p. 62), printed p. 62 (PDF 64)

import Mathlib
import Definitions.Def_SATComputability
import Definitions.Def_KSATSingleFlip_Connect_Model
import Definitions.Def_KSATSingleFlip_Connect_FactorGraph
import Definitions.Def_KSATSingleFlip_Connect_Repair

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

/-- Lemma 7.11 (small-set bounds for repair; printed p. 62). For `0 ≤ m ≤ (2^k n/k)(ln k + ln ln k
+ 1 + (ln ln k + 1/2)/ln k − 6(ln ln k)²/(ln k)²)` and fixed `x`: `Φ₀` has `Pois(m(1 − 2^{−k}))`
independent uniform `k`-clauses satisfied by `x`, `G` independently `Pois(m)` independent uniform
`k`-clauses. With probability at least `1 − e^{−ρ^8 n}`, the bounds (i)–(iii) hold for every `Φ⁺`
with `Φ₀ ⊆ Φ⁺ ⊆ Φ₀ ∪ G`, i.e. `Φ⁺` = the clauses of `Φ₀` (positions `I₀`, the first ones) followed
by a sub-formula of `G` (positions `I`). -/
theorem lemma_7_11 :
    ∃ k0 : ℕ, ∀ k ≥ k0, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ m : ℝ, 0 ≤ m →
      m ≤ (2 : ℝ) ^ k * n / k * loosenessLambda k →
      ∀ x : Fin n → Bool,
        1 - Real.exp (-(rho k ^ 8) * n) ≤
          poisExp (clausesSatBy (k := k) (fun _ : Fin 1 => x)) (m * (1 - 1 / (2 : ℝ) ^ k))
            (fun l0 => poisProb (allClauses n k) m (fun g =>
              ∀ I : Finset (Fin (ofList g).length),
                RepairBounds k (ofList l0 ++ subF (ofList g) I)
                  (Finset.univ.filter fun c => c.val < (ofList l0).length) x)) := by sorry

end KSATSingleFlip.Connect
